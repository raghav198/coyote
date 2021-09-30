def calc_determinant(matrix):
        determinant = 0
        indices = list(range(len(matrix)))
        # For 2x2
        if len(matrix) == 2 and len(matrix[0]) == 2:
            val = matrix[0][0] * matrix[1][1] + -(matrix[1][0] * matrix[0][1])
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
        output_matrix = [[sum(a*b for a,b in zip(X_row,Y_col)) for Y_col in zip(*matrix2)] for X_row in matrix1]
        return(output_matrix)

def benchmark(matrix1, matrix2):
    result_matrix = matrix_multiply(matrix1, matrix2)
    determinant = calc_determinant(result_matrix)
    return(determinant)