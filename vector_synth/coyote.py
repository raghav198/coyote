from multiply_determinant_kernel import get_2x2_determinant
from ast_def import *
from random import seed
from sys import argv
from vector_compiler import vector_compile
import os
import shutil
from benchmarks.mat_mul_det import *
from benchmarks.mat_convol import *
from benchmarks.pairwise_dist import *
from benchmarks.mat_mult import *
from benchmarks.dot_product import *
from numberTreeGenerator import *

if __name__ == '__main__':
    ### Change name to whatever you want the directory name to be
    directory = "dot_product6x6"
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

    seed(33)
    exprs = [fuzzer(0.7) for _ in range(4)]
    
    # expr = get_2x2_determinant()
    # input_groups = [{
    #     'a:0,0', 'a:0,1', 'a:0,2',
    #     'a:1,0', 'a:1,1', 'a:1,2',
    #     'a:2,0', 'a:2,1', 'a:2,2'}, {
    #         'b:0,0', 'b:0,1', 'b:0,2',
    #         'b:1,0', 'b:1,1', 'b:1,2',
    #         'b:2,0', 'b:2,1', 'b:2,2'}]
    # c = Compiler({}, input_groups)

    # exprs = [expr]

    ######################################################
    
    ## Matrix Multiply Determinant Benchmark
    # input_groups = get_mmd_input_groups('a', 'b', 2, 2)
    # c = Compiler({}, input_groups, allow_replicating = [0,1])

    # tag_list = []
    # tree = (mat_mul_det_benchmark(2, 2)).a
    # print(tree)
    # tag_list.append(c.compile(tree))
    ## End Matrix Multiply Determinant Benchmark

    

    ## Matrix Multiply Determinant Benchmark
    # input_groups = get_mmd_input_groups('a', 'b', 3, 3)
    # c = Compiler({}, input_groups, allow_replicating = [0,1])

    # tag_list = []
    # tree = (mat_mul_det_benchmark(3, 3)).a
    # print(tree)
    # tag_list.append(c.compile(tree))
    ## End Matrix Multiply Determinant Benchmark

    ######################################################

    ## Matrix Convolution Benchmark
    # input_groups = get_mc_input_groups('a', 'b', 4, 4, 2, 2)
    # c = Compiler({}, input_groups, allow_replicating = [0,1])

    # tag_list = []
    # for i in mat_convol_benchmark(4, 2):
    #     for j in range(4 - 2 + 1):
    #         tree = i[j].a
    #         print(tree)
    #         tag_list.append(c.compile(tree))
    ## End Matrix Convolution Benchmark

    # ## Matrix Convolution Benchmark
    # input_groups = get_mc_input_groups('a', 'b', 4, 4, 3, 3)
    # c = Compiler({}, input_groups, allow_replicating = [0,1])

    # tag_list = []
    # for i in mat_convol_benchmark(4, 3):
    #     for j in range(4 - 3 + 1):
    #         tree = i[j].a
    #         print(tree)
    #         tag_list.append(c.compile(tree))
    # ## End Matrix Convolution Benchmark

    ######################################################

    ## Pairwise Distance Benchmark
    # input_groups = get_pd_input_groups('a', 'b', 'c', 'd', 2, 2)
    # c = Compiler({}, input_groups, allow_replicating = [0,1,2,3])

    # tag_list = []
    # for i in pairwise_dist_benchmark(2, 2):
    #     tree = i.a
    #     print(tree)
    #     tag_list.append(c.compile(tree))
    ## End Pairwise Distance Benchmark

    # ## Pairwise Distance Benchmark
    # input_groups = get_pd_input_groups('a', 'b', 'c', 'd', 4, 4)
    # c = Compiler({}, input_groups, allow_replicating = [0,1,2,3])

    # tag_list = []
    # for i in pairwise_dist_benchmark(4, 4):
    #     tree = i.a
    #     print(tree)
    #     tag_list.append(c.compile(tree))
    # ## End Pairwise Distance Benchmark

    ######################################################

    ## Matrix Multiply Benchmark
    # input_groups = get_mm_input_groups('a', 'b', 2, 2)
    # c = Compiler({}, input_groups, allow_replicating = [0,1])

    # tag_list = []
    # for i in mat_mult_benchmark(2, 2):
    #     for j in range(2):
    #         tree = i[j].a
    #         print(tree)
    #         tag_list.append(c.compile(tree))
    ## End Matrix Multiply Benchmark

    ## Matrix Multiply Benchmark
    # input_groups = get_mm_input_groups('a', 'b', 3, 3)
    # c = Compiler({}, input_groups, allow_replicating = [0,1])

    # tag_list = []
    # for i in mat_mult_benchmark(3, 3):
    #     for j in range(3):
    #         tree = i[j].a
    #         print(tree)
    #         tag_list.append(c.compile(tree))
    ## End Matrix Multiply Benchmark

    ######################################################

    ## Dot Product Benchmark
    # input_groups = get_dp_input_groups('a', 'b', 3, 3)
    # c = Compiler({}, input_groups, allow_replicating = [0,1])

    # tag_list = []
    # tree = dot_product_benchmark(3, 3).a
    # print(tree)
    # tag_list.append(c.compile(tree))
    ## End Dot Prodcut Benchmark

    ## Dot Product Benchmark
    input_groups = get_dp_input_groups('a', 'b', 6, 6)
    c = Compiler({}, input_groups, allow_replicating = [0,1])

    tag_list = []
    tree = dot_product_benchmark(6, 6).a
    print(tree)
    tag_list.append(c.compile(tree))
    ## End Dot Prodcut Benchmark

    ######################################################

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