import sys 
sys.path.append('..')
from ast_def import *

def dot_prod(arr1, arr2):
    output = Tree(0)
    products = [Tree(0) for i in arr1]
    for i in range(len(arr1)):
        products[i] = arr1[i] * arr2[i]
    currentlevel = []
    nextlevel = []
    currentlevel = products
    while (len(currentlevel) != 1):
        if (len(currentlevel) % 2 == 0):
            for i in range(int(len(currentlevel)/2)):
                nextlevel.append(currentlevel[2*i] + currentlevel[2*i + 1])
        else:
            nextlevel.append(currentlevel[0])
            currentlevel = currentlevel[1:]
            for i in range(int(len(currentlevel)/2)):
                nextlevel.append(currentlevel[2*i] + currentlevel[2*i + 1])
        currentlevel = nextlevel
        nextlevel = []
    output = currentlevel
    return(output)

def array_generator(char1, nels):
    array = [Tree(Var(char1 + ":" + str(n))) for n in range(nels)]
    return(array)

def get_dp_input_groups(char1, char2, nels1, nels2):
    input_groups = []
    set1 = [(char1 + ":" + str(n)) for n in range(nels1)]
    set2 = [(char2 + ":" + str(n)) for n in range(nels2)]
    input_groups = [{i for i in set1}, {i for i in set2}]
    return input_groups

def pairwise_dist_benchmark(nels1, nels2):
    array1 = array_generator('a', nels1)
    array2 = array_generator('b', nels2)
    distance = dot_prod(array1, array2)
    for i in distance:
        print(i.a)
    return(distance)

pairwise_dist_benchmark(6,6)