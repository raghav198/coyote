from multiply_determinant_kernel import get_2x2_determinant
from ast_def import Compiler, fuzzer
from random import seed
from sys import argv
from vector_compiler import vector_compile
import os
import shutil

if __name__ == '__main__':
    ### Change name to whatever you want the directory name to be
    directory = "test"
    ###
    path = os.path.join("outputs/", directory)
    shutil.rmtree(path)
    os.mkdir(path)
    argv.append(path + "/scal")
    argv.append(path + "/vec")
    if len(argv) != 3:
        print(f'Usage: {argv[0]} [scalar_output] [vector_output]')
        raise SystemExit()

    scalar_file = argv[1]
    vector_file = argv[2]
    print("Scalarfile", scalar_file)
    print("Vectorfile", vector_file)

    # expr = get_2x2_determinant()
    # input_groups = [{
    #     'a:0,0', 'a:0,1', 'a:0,2',
    #     'a:1,0', 'a:1,1', 'a:1,2',
    #     'a:2,0', 'a:2,1', 'a:2,2'}, {
    #         'b:0,0', 'b:0,1', 'b:0,2',
    #         'b:1,0', 'b:1,1', 'b:1,2',
    #         'b:2,0', 'b:2,1', 'b:2,2'}]
    # c = Compiler({}, input_groups)

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

    def calc_matrix_mult_det(matrix1, matrix2):
        determinant = calc_determinant(matrix1) * calc_determinant(matrix2)

    seed(33)
    exprs = [fuzzer(0.7) for _ in range(4)]
    # exprs = [expr]

    c = Compiler({})
    tag_list = []
    for expr in exprs:
        tag_list.append(c.compile(expr))

    scalar_code_to_write = '\n'.join(map(str, c.code))
    scalar_code_to_write = ' '.join(map(str, tag_list)) + '\n' + scalar_code_to_write
    open(scalar_file, 'w').write(scalar_code_to_write)

    vector_code, width = vector_compile(c)
    open(vector_file, 'w').write(f'{width}\n' + '\n'.join(vector_code))

    print(f'Vector width = {width}')
    #Run compile_to_bfv.py
    os.system("python3 compile_to_bfv.py " + directory)
    #Change CMakeLists.txt to point to new C++ files
    CMake = open("bfv_backend/CMakeLists.txt", "r")
    CMake_lines = CMake.readlines()
    CMake.close() 
    for i in range(len(CMake_lines)):
        if ((CMake_lines[i].rstrip()).strip())[-10:] == "scalar.cpp":
            CMake_lines[i] = "\t" + "\t" + "\t" + directory + "/scalar.cpp" + "\n"
        elif ((CMake_lines[i].rstrip()).strip())[-10:] == "vector.cpp":
            CMake_lines[i] = "\t" + "\t" + "\t" + directory + "/vector.cpp" + "\n"
    new_file_contents = "".join(CMake_lines)
    CMake = open("bfv_backend/CMakeLists.txt", "w")
    CMake.write(new_file_contents)
    CMake.close()
    #Build and run the CMake project
    # os.chdir("bfv_backend")
    # os.system("cmake --build build")
    # os.chdir("build")
    # os.system("make all")