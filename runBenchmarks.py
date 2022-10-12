import os

benchmarks = ['decision_tree', 'distances_5x5_fully', 'distances_4x4_fully',
             'distances_3x3_fully', 'matmul_2x2_fully', 'matmul_3x3_fully', 
             'conv_4x2_fully', 'conv_5x3_fully', 'dot_product_3x3_fully',
             'dot_product_6x6_fully', 'dot_product_10x10_fully', 
             'decision_tree_packed_fully', 'distances_5x5_partially',
             'distances_4x4_partially', 'distances_3x3_partially', 
             'matmul_2x2_partially', 'matmul_3x3_partially', 'conv_4x2_partially',
             'conv_5x3_partially', 'dot_product_3x3_partially', 
             'dot_product_6x6_partially', 'dot_product_10x10_partially',
             'decision_tree_packed_partially', 'distances_5x5_un', 'distances_4x4_un',
             'distances_3x3_un', 'matmul_2x2_un', 'matmul_3x3_un', 'conv_4x2_un',
             'conv_5x3_un', 'dot_product_3x3_un', 'dot_product_6x6_un',
             'dot_product_10x10_un', 'decision_tree_packed_un', 'matmul_3x3_case1',
             'matmul_3x3_case2', 'matmul_3x3_case3', 'matmul_3x3_case4', 
             'matmul_3x3_case5']

benchmarks = ['max_value']

for benchmark in benchmarks:
    os.system("python3 benchmarks.py build " + benchmark)
    os.system("python3 compile_to_bfv.py " + benchmark)
