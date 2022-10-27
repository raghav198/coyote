import os

benchmarks = ['distances_5x5_fully',
             'conv_4x2_fully', 'conv_5x3_fully', 'dot_product_3x3_fully',
             'dot_product_6x6_fully', 'dot_product_10x10_fully', 
             'distances_5x5_partially',
             'conv_4x2_partially',
             'conv_5x3_partially', 'dot_product_3x3_partially', 
             'dot_product_6x6_partially', 'dot_product_10x10_partially',
             'distances_5x5_un', 'conv_4x2_un',
             'conv_5x3_un', 'dot_product_3x3_un', 'dot_product_6x6_un',
             'dot_product_10x10_un']

def collect_data(benchmark):
    os.system("./build/" + benchmark)

for benchmark in benchmarks:
    collect_data(benchmark)

# collect_data("mat_mul_det2x2")
# collect_data("mat_mul_det3x3")
# collect_data("mat_convol4x4x2x2")
# collect_data("mat_convol4x4x3x3")
# collect_data("pairwise_dist2x2")
# collect_data("pairwise_dist3x3")
# collect_data("mat_mult2x2")
# collect_data("mat_mult3x3")
# collect_data("dot_product3x3")
# collect_data("dot_product6x6")

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

# collect_data("max_value")