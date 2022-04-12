import os

benchmarks = ['tree_100-100-5_1', 'tree_100-100-5_2', 'tree_100-100-5_3',
              'tree_100-100-5_4', 'tree_100-100-5_5', 'tree_100-100-10_1',
              'tree_100-100-10_2', 'tree_100-100-10_3', 'tree_100-100-10_4', 
              'tree_100-100-10_5', 'tree_100-50-5_1', 'tree_100-50-5_2', 
              'tree_100-50-5_3', 'tree_100-50-5_4', 'tree_100-50-5_5', 
              'tree_100-50-10_1', 'tree_100-50-10_2', 'tree_100-50-10_3',
              'tree_100-50-10_4', 'tree_100-50-10_5', 'tree_50-50-5_1',
              'tree_50-50-5_2', 'tree_50-50-5_3', 'tree_50-50-5_4',
              'tree_50-50-5_5', 'tree_50-50-10_1', 'tree_50-50-10_2',
              'tree_50-50-10_3', 'tree_50-50-10_4', 'tree_50-50-10_5']

for benchmark in benchmarks:
    print(benchmark + ": ")
    os.system("cat " +  benchmark + ".csv | tail -n +2 | cut -d , -f 3,7 | sed 's|,|/|' | bc -l | awk '{s+=$1} END {print 50 / 50}'")
    