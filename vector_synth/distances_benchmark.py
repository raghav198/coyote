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

if __name__ == '__main__':
    exprs = get_distances('a', 'b', 3)
    input_groups = [{'a_x0', 'a_x1', 'a_x2', 'a_x3'}, {'b_x0', 'b_x1', 'b_x2', 'b_x3'}]
    c = Compiler({}, input_groups, allow_replicating=[1])
    for expr in exprs:
        c.compile(expr)
    print('\n'.join(map(str, c.code)))
    # raise SystemExit()
    vectorized, width = vector_compile(c)
    print('\n'.join(vectorized))