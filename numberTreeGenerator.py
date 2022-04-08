#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jul 18 18:45:15 2021

@author: kabirsheth
"""
import random as rand
from typing import List, Union
from dataclasses import dataclass
from inspect import signature
from coyote.coyote_ast import CompilerV2, Var, Tree, Op
from coyote.vectorize_circuit import vectorize

Expression = Union['Var', 'Op']

def treeGenerator(maxDepth, inputSeed) -> Expression:
    global seed 
    seed = inputSeed
    rand.seed(seed)
    localString = ""
    if (maxDepth > 0):
        randomNum = rand.randrange(0,1)
        seed+=1
        if (randomNum > 1):
            localString+=str(rand.randrange(0,1024))
            seed+=1
            return Tree(Var(localString))
        else:
            lhs = treeGenerator(maxDepth-1, seed)
            rhs = treeGenerator(maxDepth-1, seed)
            if (randomNum == 1):
                return(lhs + rhs)
            elif (randomNum == 0):
                return(lhs * rhs)
    else:
        endNode = str(rand.randrange(0,1024))
        seed+=1
        return Tree(Var(endNode))

class coyote_compiler:
    def __init__(self):
        self.func_signatures = {}
        self.outputs = []

    def vectorize(self):
        return vectorize(self.compiler)


    def instantiate(self, seed):
        outputs = []
        output = treeGenerator(3, seed)
        outputs.append(output)
        self.compiler = CompilerV2([])
        for out in outputs:
            print(type(out.a))
            self.outputs.append(self.compiler.compile(out.a).val)

        return [' '.join(f'%{reg}' for reg in self.outputs)] + list(map(str, self.compiler.code))



if __name__ == '__main__':
    coyote = coyote_compiler()

    total_rotates = []
    for i in range(20):
        scalar_code = coyote.instantiate(1661)
        vectorized_code, width = coyote.vectorize()
        print('\n'.join(scalar_code))
        print(ans := '\n'.join(vectorized_code))
        total_rotates.append(ans.count('>>'))

    print(sum(total_rotates) / 20, min(total_rotates), max(total_rotates), total_rotates)