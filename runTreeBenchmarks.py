import os

# benchmarks = ['tree_100-100-5_1', 'tree_100-100-5_2', 'tree_100-100-5_3',
#               'tree_100-100-5_4', 'tree_100-100-5_5', 'tree_100-100-10_1',
#               'tree_100-100-10_2', 'tree_100-100-10_3', 'tree_100-100-10_4', 
#               'tree_100-100-10_5']

benchmarks = ['tree_100-50-10_1',
              'tree_100-50-10_2', 'tree_100-50-10_3', 'tree_100-50-10_4', 
              'tree_100-50-10_5']

# benchmarks = ['tree_50-50-5_1', 'tree_50-50-5_2', 'tree_50-50-5_3',
#               'tree_50-50-5_4', 'tree_50-50-5_5', 'tree_50-50-10_1',
#               'tree_50-50-10_2', 'tree_50-50-10_3', 'tree_50-50-10_4', 
#               'tree_50-50-10_5']

for benchmark in benchmarks:
    os.system("python3 numberTreeGenerator.py build " + benchmark)
    os.system("python3 compile_to_bfv.py " + benchmark)