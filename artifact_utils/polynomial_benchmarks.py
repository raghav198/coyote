import argparse
import os



depths = ['5', '10']
regimes = ['50-50', '100-50', '100-100']


parser = argparse.ArgumentParser()
parser.add_argument('-d', '--depths', nargs='+', choices=depths, required=True)
parser.add_argument('-r', '--regimes', nargs='+', choices=regimes, required=True)
parser.add_argument('-i', '--iters', type=int, required=True)

args = parser.parse_args()

for regime in args.regimes:
    for depth in args.depths:
        for i in range(args.iters):
            benchmark = f'tree_{regime}-{depth}_{i+1}'
            print(f'Benchmark {benchmark}...')
            os.system(f'python3 numberTreeGenerator.py build {benchmark}')
            os.system(f'python3 compile_to_bfv.py {benchmark}')


# benchmarks = ['tree_100-100-5_1', 'tree_100-100-5_2', 'tree_100-100-5_3',
#               'tree_100-100-5_4', 'tree_100-100-5_5', 'tree_100-100-10_1',
#               'tree_100-100-10_2', 'tree_100-100-10_3', 'tree_100-100-10_4', 
#               'tree_100-100-10_5']

# benchmarks = ['tree_100-50-10_1',
#               'tree_100-50-10_2', 'tree_100-50-10_3', 'tree_100-50-10_4', 
#               'tree_100-50-10_5']

# # benchmarks = ['tree_50-50-5_1', 'tree_50-50-5_2', 'tree_50-50-5_3',
# #               'tree_50-50-5_4', 'tree_50-50-5_5', 'tree_50-50-10_1',
# #               'tree_50-50-10_2', 'tree_50-50-10_3', 'tree_50-50-10_4', 
# #               'tree_50-50-10_5']

# for benchmark in benchmarks:
#     os.system("python3 numberTreeGenerator.py build " + benchmark)
#     os.system("python3 compile_to_bfv.py " + benchmark)