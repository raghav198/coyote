import sys 
sys.path.append('..')
from ast_def import *

def dot_prod(arr1, arr2):
    output = Tree(0)
    products = [Tree(0) for i in arr1]
    for i in range(len(arr1)):
        products[i] = arr1[i] * arr2[i]
    output = recursive_sum(products)
    return(output)

def recursive_sum(products):
    overallsum = Tree(0)
    if (len(products) > 2):
        sum1 = recursive_sum(products[0:int(len(products)/2)])
        sum2 = recursive_sum(products[int(len(products)/2):])
        overallsum = sum1 + sum2
    elif (len(products) == 2):
        sum1 = products[0]
        sum2 = products[1]
        overallsum = sum1 + sum2
    elif (len(products) == 1):
        overallsum = products[0]
    return(overallsum)
        
def array_generator(char1, nels):
    array = [Tree(Var(char1 + ":" + str(n))) for n in range(nels)]
    return(array)

def get_dp_input_groups(char1, char2, nels1, nels2):
    input_groups = []
    set1 = [(char1 + ":" + str(n)) for n in range(nels1)]
    set2 = [(char2 + ":" + str(n)) for n in range(nels2)]
    input_groups = [{i for i in set1}, {i for i in set2}]
    return input_groups

def dot_product_benchmark(nels1, nels2):
    array1 = array_generator('a', nels1)
    array2 = array_generator('b', nels2)
    distance = dot_prod(array1, array2)
    print(distance.a)
    return(distance)