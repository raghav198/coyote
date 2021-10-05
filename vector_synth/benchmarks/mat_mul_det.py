from ast_def import *
def calc_determinant(matrix):
        determinant = 0
        indices = list(range(len(matrix)))
        # For 2x2
        if len(matrix) == 2 and len(matrix[0]) == 2:
            val = matrix[0][0] * matrix[1][1] + (matrix[1][0] * matrix[0][1])
            return val
        # Recursive path for larger matrices
        for column in indices:
            copy = copy_matrix(matrix)
            copy = copy[1:]
            height = len(copy)
    
            for i in range(height): 
                copy[i] = copy[i][0:column] + copy[i][column+1:] 
            if (column % 2 == 0):
                sign = 1
            else:
                sign = -1

            sub_det = determinant_recursive(copy)
            total += sign * matrix[0][column] * sub_det 
        return determinant

def matrix_multiply(matrix1, matrix2):
        output_matrix = [[Tree(0), Tree(0)],[Tree(0), Tree(0)]]
        for i in range(len(matrix1)):
            for j in range(len(matrix2[0])):
                for k in range(len(matrix2)):
                    output_matrix[i][j] = output_matrix[i][j] + matrix1[i][k] * matrix2[k][j]
        return(output_matrix)

def mat_mul_det_benchmark(matrix1, matrix2):
    result_matrix = matrix_multiply(matrix1, matrix2)
    determinant = calc_determinant(result_matrix)
    return(determinant)