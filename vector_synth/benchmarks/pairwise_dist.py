import sys 
sys.path.append('..')
from ast_def import *

def calc_distance(arr1, arr2):
    output = [Tree(0) for i in arr1 for j in arr2]
    for i in range(len(arr1)):
        for j in range(len(arr2)):
            output[len(arr1) * i + j] = (arr1[i][0] + arr2[j][0]) * (arr1[i][0] + arr2[j][0]) - (arr1[i][1] + arr2[j][1]) * (arr1[i][1] + arr2[j][1]) 
    return(output)

def array_generator(char1, char2, nels):
    array = [[Tree(Var(char1 + ":" + str(n))), Tree(Var(char2 + ":" + str(n)))] for n in range(nels)]
    return(array)

def get_pd_input_groups(char1, char2, char3, char4, nels1, nels2):
    input_groups = []
    set1 = [(char1 + ":" + str(n)) for n in range(nels1)]
    set2 = [(char2 + ":" + str(n)) for n in range(nels1)]
    set3 = [(char3 + ":" + str(n)) for n in range(nels2)]
    set4 = [(char4 + ":" + str(n)) for n in range(nels2)]
    input_groups = [{i for i in set1}, {i for i in set2}, {i for i in set3}, {j for j in set4}]
    return input_groups

def pairwise_dist_benchmark(nels1, nels2):
    array1 = array_generator('a', 'b', nels1)
    array2 = array_generator('c', 'd', nels2)
    distance = calc_distance(array1, array2)
    return(distance)