import sys 
sys.path.append('..')
from ast_def import *

def calc_distance(arr1, arr2):
    output = [Tree(0) for i in arr1 for j in arr2]
    for i in range(len(arr1)):
        for j in range(len(arr2)):
            output[len(arr1) * i + j] = (arr1[i][0] + arr2[j][0]) * (arr1[i][0] + arr2[j][0]) + (arr1[i][1] + arr2[j][1]) * (arr1[i][1] + arr2[j][1]) 
    return(output)

def array_generator(char1, char2, nels):
    array = [[Tree(Var(char1 + ":" + str(n))), Tree(Var(char2 + ":" + str(n)))] for n in range(nels)]
    return(array)

def get_input_groups(char1, char2, char3, char4, nels1, nels2):
    input_groups = []
    set1 = [[(char1 + ":" + str(n)), (char2 + ":" + str(n))] for n in range(nels1)]
    set2 = [[(char3 + ":" + str(n)), (char4 + ":" + str(n))] for n in range(nels2)]
    input_groups = [{tuple(i) for i in set1}, {tuple(j) for j in set2}]
    return input_groups

def pairwise_dist_benchmark():
    array1 = array_generator('a', 'b', 5)
    array2 = array_generator('c', 'd', 5)
    distance = calc_distance(array1, array2)
    return(distance)