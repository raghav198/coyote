#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jul 18 18:45:15 2021

@author: kabirsheth
"""
import random
from typing import List, Union

seed=1000;
Expression = Union['Var', 'Op'];

class Var:
    def __init__(self, name: str):
        self.name = name
        self.tag = name
        self.subtags: List[Union[int, str]] = []

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return f'Var("{self.name}")'

    def __eq__(self, o: object) -> bool:
        return isinstance(o, Var) and o.name == self.name


class Op:
    def __init__(self, op: str, lhs: Expression, rhs: Expression):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs
        self.tag: int = -1
        self.subtags: List[Union[int, str]] = []

    def __str__(self) -> str:
        return f'({str(self.lhs)} {self.op} {str(self.rhs)})'

    def __repr__(self) -> str:
        return f'Op("{self.op}", {repr(self.lhs)}, {repr(self.rhs)})'

    def __eq__(self, o: object) -> bool:
        return isinstance(o, Op) and o.op == self.op and o.lhs == self.lhs and o.rhs == self.rhs
    
def plus(a, b):
    if type(a) is str:
        a = Var(a)
    if type(b) is str:
        b = Var(b)

    return Op('+', a, b)


def times(a, b):
    if type(a) is str:
        a = Var(a)
    if type(b) is str:
        b = Var(b)

    return Op('*', a, b)


def treeGenerator(maxDepth) -> Expression:
    global seed
    random.seed(seed);
    localString = "";
    if (maxDepth > 0):
        randomNum = random.randrange(0,3);
        seed+=1;
        print("randomNum", randomNum)
        if (randomNum == 0):
            localString+=str(random.randrange(0,1024));
            seed+=1;
            print("localString", localString);
            return Var(localString);
        else:
            lhs = treeGenerator(maxDepth-1);
            print("lhs", lhs)
            rhs = treeGenerator(maxDepth-1);
            print("rhs", rhs)
            
            if (randomNum == 1):
                print(plus(lhs,rhs))
                return(plus(lhs,rhs))
            elif (randomNum == 2):
                print(times(lhs,rhs))
                return(times(lhs,rhs))
    else:
        endNode = str(random.randrange(0,1024));
        seed+=1;
        return Var(endNode);

treeGenerator(2)