import os

base = "/Users/malik22/efficient-FHE-compiler"
cmake = "/opt/homebrew/bin/cmake"

def collect_data(benchmark):
    CMake = open("CMakeLists.txt", "r")
    CMake_lines = CMake.readlines()
    CMake.close() 
    for i in range(len(CMake_lines)):
            if ((CMake_lines[i].rstrip()).strip())[-10:] == "scalar.cpp":
                CMake_lines[i] = "\t" + benchmark + "/scalar.cpp" + "\n"
            elif ((CMake_lines[i].rstrip()).strip())[-10:] == "vector.cpp":
                CMake_lines[i] = "\t" + benchmark + "/vector.cpp" + "\n"
    new_file_contents = "".join(CMake_lines)
    CMake = open("CMakeLists.txt", "w")
    CMake.write(new_file_contents)
    CMake.close()

    main = open("main.cpp", "r")
    main_lines = main.readlines()
    main.close() 
    for i in range(len(main_lines)):
            if ((main_lines[i].rstrip()).strip())[0:20] == "std::ofstream myfile":
                main_lines[i] = 'std::ofstream myfile(' + '"' + benchmark + ".csv" + '"' + ');\n'
    new_file_contents = "".join(main_lines)
    main = open("main.cpp", "w")
    main.write(new_file_contents)
    main.close()

    os.system("/usr/local/bin/cmake --build /Users/kabirsheth/efficient-FHE-compiler/vector_synth/bfv_backend/build --config Release --target all -j 10 --")
    os.system("/Users/kabirsheth/efficient-FHE-compiler/vector_synth/bfv_backend/build/CoyoteBFVBackend")

# collect_data("mat_mul_det2x2")
# collect_data("mat_mul_det3x3")
# collect_data("mat_convol4x4x2x2")
# collect_data("mat_convol4x4x3x3")
# collect_data("pairwise_dist2x2")
# collect_data("pairwise_dist3x3")
collect_data("mat_mult2x2")
collect_data("mat_mult3x3")
collect_data("dot_product3x3")
collect_data("dot_product6x6")

# collect_data("tree50,50-3_1")
# collect_data("tree50,50-3_2")
# collect_data("tree50,50-3_3")
# collect_data("tree50,50-3_4")
# collect_data("tree50,50-3_5")
# collect_data("tree50,50-6_1")
# collect_data("tree50,50-6_2")
# collect_data("tree50,50-6_3")
# collect_data("tree50,50-6_4")
# collect_data("tree50,50-6_5")

# collect_data("tree100,50-3_1")
# collect_data("tree100,50-3_2")
# collect_data("tree100,50-3_3")
# collect_data("tree100,50-3_4")
# collect_data("tree100,50-3_5")
# collect_data("tree100,50-6_1")
# collect_data("tree100,50-6_2")
# collect_data("tree100,50-6_3")
# collect_data("tree100,50-6_4")
# collect_data("tree100,50-6_5")

# collect_data("tree100,100-3_1")
# collect_data("tree100,100-3_2")
# collect_data("tree100,100-3_3")
# collect_data("tree100,100-3_4")
# collect_data("tree100,100-3_5")
# collect_data("tree100,100-6_1")
# collect_data("tree100,100-6_2")
# collect_data("tree100,100-6_3")
# collect_data("tree100,100-6_4")
# collect_data("tree100,100-6_5")