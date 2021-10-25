from sys import stderr, stdout
from ast_def import Compiler, plus, times
from multiply_determinant_kernel import get_2x2_determinant
from vector_compiler import vector_compile
from copy import copy

def get_distances(arr1, arr2, sz):
    dists = []
    for i in range(sz):
        for j in range(sz):
            xdiff = plus(f'{arr1}_x{i}', f'{arr2}_x{j}')
            dists.append(times(xdiff, copy(xdiff)))
            print(dists[-1])
    return dists


def better_sum(arr):
    if len(arr) == 1:
        return arr[0]
    mid = len(arr) // 2
    return plus(better_sum(arr[:mid]), better_sum(arr[mid:]))

def dot_product(arr1, arr2, sz):
    prods = [times(f'{arr1}_{i}', f'{arr2}_{i}') for i in range(sz)]
    return better_sum(prods)

def create_matrix(name, rows, cols):
    matrix = []
    for i in range(rows):
        pass

if __name__ == '__main__':
    # exprs = get_distances('a', 'b', 3)
    # input_groups = [{'a_x0', 'a_x1', 'a_x2', 'a_x3'}, {'b_x0', 'b_x1', 'b_x2', 'b_x3'}]
    # c = Compiler({}, input_groups, allow_replicating=[])
    # for expr in exprs:
    #     c.compile(expr)
    # print('\n'.join(map(str, c.code)))
    # # raise SystemExit()
    # vectorized, width = vector_compile(c)
    # print('\n'.join(vectorized))

    SZ = 8

    expr = [dot_product('a', 'b', SZ)]
    print(expr[0])
    input_groups = [{f'a_{i}' for i in range(SZ)}, {f'b_{i}' for i in range(SZ)}]
    c = Compiler({}, input_groups, allow_replicating=[])
    c.compile(expr[0])
    print('\n'.join(map(str, c.code)))
    vectorized, width = vector_compile(c)
    print('\n'.join(vectorized))