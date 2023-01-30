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
from sys import argv
import os
from coyote.coyote import *

Expression = Union['Var', 'Op']

def treeGenerator(originalDepth, maxDepth, inputSeed) -> Expression:
    global seed 
    seed = inputSeed
    rand.seed(seed)
    localString = ""
    if (originalDepth == maxDepth or maxDepth == originalDepth - 1):
        randomNum = rand.randrange(0,2)
        lhs = treeGenerator(originalDepth, maxDepth-1, seed)
        rhs = treeGenerator(originalDepth, maxDepth-1, seed)
        if (randomNum == 1):
            return(lhs + rhs)
        elif (randomNum == 0):
            return(lhs * rhs)
    if (maxDepth > 0):
        randomNum = rand.randrange(0,4)
        seed+=1
        if (randomNum > 1):
            localString+=str(rand.randrange(0,1024))
            seed+=1
            print(originalDepth + 1 - maxDepth)
            return Tree(Var(localString))
        else:
            lhs = treeGenerator(originalDepth, maxDepth-1, seed)
            rhs = treeGenerator(originalDepth, maxDepth-1, seed)
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


    def instantiate(self, depth, seed):
        outputs = []
        output = treeGenerator(depth, depth, seed)
        outputs.append(output)
        self.compiler = CompilerV2([])
        for out in outputs:
            print(out.a)
            self.outputs.append(self.compiler.compile(out.a).val)

        return [' '.join(f'%{reg}' for reg in self.outputs)] + list(map(str, self.compiler.code))

def usage():
    print(f'Usage: {argv[0]} [list|build] [benchmark_name?]')
    raise SystemExit()

if __name__ == '__main__':
    coyote = coyote_compiler()

    if (int(argv[2][-3]) == 5):
        depth = 5
    else:
        depth = 10
    seed = 9100 + (int(argv[2][-1]) - 1) * 100 + (int(argv[2][-3]) * 100)
    print(depth)
    print(seed)

    # total_rotates = []
    # for i in range(20):
    #     scalar_code = coyote.instantiate(1661)
    #     vectorized_code, width = coyote.vectorize()
    #     print('\n'.join(scalar_code))
    #     print(ans := '\n'.join(vectorized_code))
    #     total_rotates.append(ans.count('>>'))

    # print(sum(total_rotates) / 20, min(total_rotates), max(total_rotates), total_rotates)

    if len(argv) < 2:
        usage()

    command = argv[1]
    if command == 'list':
        print('List of available benchmarks:')
        for func in coyote.func_signatures:
            print(f'* {func.__name__}')
    elif command == 'build':
        if len(argv) != 3:
            print(f'Error: command "build" but no benchmark was specified (try `{argv[0]} list` to list available benchmarks)')
            usage()
        benchmark_name = argv[2]
        scalar_code = coyote.instantiate(depth, seed + int(argv[2][-1]))
        vector_code = coyote.vectorize()

        try:
            os.mkdir('outputs')
        except FileExistsError:
            pass
        
        try:
            os.mkdir(f'outputs/{benchmark_name}')
        except FileExistsError:
            pass

        open(f'outputs/{benchmark_name}/scal', 'w').write('\n'.join(scalar_code))
        open(f'outputs/{benchmark_name}/vec', 'w').write('\n'.join(vector_code))
        print(f'Successfully compiled benchmark {benchmark_name}; outputs placed in "outputs/{benchmark_name}"!')