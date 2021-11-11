import sys 
sys.path.append('..')
from ast_def import *

def matrix_generator(char, rows, cols):
    matrix = [  [Tree(Var(char + ":" + str(r) + "," + str(c))) for c in range(cols)] for r in range(rows)]
    return(matrix)

def matrix_multiply(matrix1, matrix2):
        output_matrix = [[Tree(0), Tree(0)],[Tree(0), Tree(0)]]
        for i in range(len(matrix1)):
            for j in range(len(matrix2[0])):
                for k in range(len(matrix2)):
                    output_matrix[i][j] = output_matrix[i][j] + matrix1[i][k] * matrix2[k][j]
        return(output_matrix)

def matrix_convolution(matrix1, matrix2):
    dim1 = len(matrix1)
    dim2 = len(matrix2)
    if dim1 < dim2:
        minimum = dim1
    else:
        minimum = dim2
    out_dim = abs(dim1 - dim2) + 1
    output = [[Tree(0) for i in range(out_dim)] for i in range(out_dim)]
    for i in range(out_dim):
        for j in range(out_dim):
            Sum = output[i][j]
            for k in range(minimum):
                for l in range(minimum):
                    Sum = Sum + matrix2[k][l] * matrix1[i + k][j + l]
            output[i][j] = Sum
    return output

def get_mc_input_groups(char1, char2, rows1, cols1, rows2, cols2):
    input_groups = []
    set1 = [[char1 + ":" + str(r) + "," + str(c) for c in range(cols1)] for r in range(rows1)]
    set1 = set1[0] + set1[1]
    set2 = [[char2 + ":" + str(r) + "," + str(c) for c in range(cols2)] for r in range(rows2)]
    set2 = set2[0] + set2[1]
    input_groups = [{i for i in set1}, {j for j in set2}]
    return input_groups

def mat_convol_benchmark(nels1, nels2):
    mat_a = matrix_generator('a', nels1, nels1)
    mat_b = matrix_generator('b', nels2, nels2)
    result = matrix_convolution(mat_a, mat_b)
    return(result)