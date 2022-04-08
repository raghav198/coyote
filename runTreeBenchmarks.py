import os

benchmarks = ['tree_100,100-3_1', 'tree_100,100-3_2', 'tree_100,100-3_3',
              'tree_100,100-3_4', 'tree_100,100-3_5', 'tree_100,100-6_1',
              'tree_100,100-6_2', 'tree_100,100-6_3', 'tree_100,100-6_4',
              'tree_100,100-6_5']

# benchmarks = ['tree_100,50-3_1', 'tree_100,50-3_2', 'tree_100,50-3_3',
#               'tree_100,50-3_4', 'tree_100,50-3_5', 'tree_100,50-6_1',
#               'tree_100,50-6_2', 'tree_100,50-6_3', 'tree_100,50-6_4',
#               'tree_100,50-6_5']

# benchmarks = ['tree_50,50-3_1', 'tree_50,50-3_2', 'tree_50,50-3_3',
#               'tree_50,50-3_4', 'tree_50,50-3_5', 'tree_50,50-6_1',
#               'tree_50,50-6_2', 'tree_50,50-6_3', 'tree_50,50-6_4',
#               'tree_50,50-6_5']

for benchmark in benchmarks:
    os.system("python3 numberTreeGenerator.py build " + benchmark)
    os.system("python3 compile_to_bfv.py " + benchmark)