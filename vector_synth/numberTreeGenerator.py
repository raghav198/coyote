#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jul 18 18:45:15 2021

@author: kabirsheth
"""
import random as rand
from typing import List, Union
from ast_def import *

Expression = Union['Var', 'Op']

def treeGenerator(maxDepth, inputSeed) -> Expression:
    global seed 
    seed = inputSeed
    rand.seed(seed)
    localString = ""
    if (maxDepth > 0):
        randomNum = rand.randrange(0,3)
        seed+=1
        if (randomNum == 0):
            localString+=str(rand.randrange(0,1024))
            seed+=1
            return Tree(Var(localString))
        else:
            lhs = treeGenerator(maxDepth-1, seed)
            rhs = treeGenerator(maxDepth-1, seed)
            if (randomNum == 1):
                return(Tree(lhs) + Tree(rhs))
            elif (randomNum == 2):
                return(Tree(lhs) * Tree(rhs))
    else:
        endNode = str(rand.randrange(0,1024))
        seed+=1
        return Tree(Var(endNode))
