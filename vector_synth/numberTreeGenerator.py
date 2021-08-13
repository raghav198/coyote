#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jul 18 18:45:15 2021

@author: kabirsheth
"""
import random as rand
from typing import List, Union
from ast_def import *

seed=1000;
Expression = Union['Var', 'Op'];

def treeGenerator(maxDepth) -> Expression:
    global seed
    rand.seed(seed);
    localString = "";
    if (maxDepth > 0):
        randomNum = rand.randrange(0,3);
        seed+=1;
        print("randomNum", randomNum)
        if (randomNum == 0):
            localString+=str(rand.randrange(0,1024));
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
        endNode = str(rand.randrange(0,1024));
        seed+=1;
        return Var(endNode);