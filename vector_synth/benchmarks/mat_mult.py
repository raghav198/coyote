import sys 
sys.path.append('..')
from ast_def import *

def matrix_multiply(matrix1, matrix2):
        output_matrix = [[Tree(0) for i in matrix1] for i in matrix2[0]]
        for i in range(len(matrix1)):
            for j in range(len(matrix2[0])):
                for k in range(len(matrix2)):
                    output_matrix[i][j] = output_matrix[i][j] + matrix1[i][k] * matrix2[k][j]
        return(output_matrix)

def matrix_generator(char, rows, cols):
    matrix = [  [Tree(Var(char + ":" + str(r) + "," + str(c))) for c in range(cols)] for r in range(rows)]
    return(matrix)

def get_mm_input_groups(char1, char2, rows, cols):
    input_groups = []
    set1 = [[char1 + ":" + str(r) + "," + str(c) for c in range(cols)] for r in range(rows)]
    newset1 = set1[0]
    for i in range(1, rows):
        newset1 += set1[i]
    set2 = [[char2 + ":" + str(r) + "," + str(c) for c in range(cols)] for r in range(rows)]
    newset2 = set2[0]
    for i in range(1, rows):
        newset2 += set2[i]
    input_groups = [{i for i in newset1}, {j for j in newset2}]
    return input_groups

def mat_mult_benchmark(nels1, nels2):
    matrix1 = matrix_generator('a', nels1, nels1)
    matrix2 = matrix_generator('b', nels2, nels2)
    result_matrix = matrix_multiply(matrix1, matrix2)
    return(result_matrix)
