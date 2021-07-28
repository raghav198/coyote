#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Created on Sun Jul 18 18:45:15 2021

@author: kabirsheth
"""
import random

treeArray = [];   
seed=1000;
depth=0;
def treeGenerator(maxDepth):
    global seed
    global depth
    depth+=1
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
            return(localString);
        elif (randomNum == 1):
            localString+="A";
        elif (randomNum == 2):
            localString+="M";
        lhs = treeGenerator(maxDepth-1);
        depth-=1
        print("lhs", lhs)
        
        rhs = treeGenerator(maxDepth-1);
        depth-=1
        print("rhs", rhs)
        
        localString+="["+str(lhs)+","+str(rhs)+"]";
        print("localString", localString)
        
        if depth==1:
            treeArray.append(localString)
        print("treeArray", treeArray)
        return(localString)
    else:
        endNode = str(random.randrange(0,1024));
        seed+=1;
        return(endNode);

treeGenerator(2)
if treeArray == []:
    treeArray.append(str(random.randrange(0,1024)))
for i in treeArray:
    for j in treeArray:
        if (treeArray.index(i)!=treeArray.index(j)):
            if j in i:
                treeArray.remove(j)
print(treeArray);