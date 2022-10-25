import numpy as np
import os

from matplotlib import pyplot as plt

csv_speedup = lambda name: (lambda arr: (arr[1:, 2] / arr[1:, 6]).mean())(np.genfromtxt(name, delimiter=','))

##############################
## PLOTTING VECTOR SPEEDUPS ##
##############################

benchmarks = ['distances', 'conv', 'matmul', 'dot_product']

names = {'distances': 'dist', 'conv': 'conv', 'matmul': 'mm', 'dot_product': 'dot'}
sizes = lambda s: (lambda a, b: a if a == b else f'{a}.{b}')(*s.split('x'))

speedups = {}

for benchmark in benchmarks:
    for size in os.listdir(f'csvs/{benchmark}'):
        u = 1 / csv_speedup(f'csvs/{benchmark}/{size}/{benchmark}_{size}_un.csv')
        p = 1 / csv_speedup(f'csvs/{benchmark}/{size}/{benchmark}_{size}_partially.csv')
        f = 1 / csv_speedup(f'csvs/{benchmark}/{size}/{benchmark}_{size}_fully.csv')

        speedups[f'{names[benchmark]}.{sizes(size)}'] = (u, p, f)

width = 0.2

speedups['sort[3]'] = tuple(1 / csv_speedup(f'csvs/decision_tree/decision_tree_packed_{suf}.csv') for suf in 'un,partially,fully'.split(','))
speedups['max[5]'] = tuple(1 / csv_speedup(f'csvs/max_value/max_value_packed_{suf}.csv') for suf in 'un,partially,fully'.split(','))

dtree_scalar_speedup = 1 / csv_speedup('csvs/decision_tree/decision_tree.csv')
max_scalar_speedup = 1 / csv_speedup('csvs/max_value/max_value.csv')

labels = [(lambda n, s: (n, eval(s)))(*l.split('.', 1)) for l in speedups.keys() if '.' in l]
labels = list(map(lambda l: f'{l[0]}.{l[1]}', sorted(labels))) + ['sort[3]', 'max[5]']
values = [speedups[l] for l in labels]

x = np.arange(len(labels))
# labels, values = zip(*sorted(zip(labels, values)))
# labels = labels[:-1] + ('dtree',)


us, ps, fs = zip(*values)
# plt.bar(x-2*width, np.ones(len(labels)), width, color='black')
plt.bar(x-width, us, width, color='#253494')
plt.bar(x, ps, width, color='#2c7fb8')
plt.bar(x+width, fs, width, color='#41b6c4')
plt.bar(labels.index('sort[3]')+width*2, dtree_scalar_speedup, width, color='#a1dab4')
plt.bar(labels.index('max[5]')+width*2, max_scalar_speedup, width, color='#a1dab4')
plt.xticks(x, labels, rotation=30)
plt.axhline(1, color='red')
plt.ylabel('(Normalized) Speedup')
# plt.legend(['Scalar', 'Unreplicated', 'Partially Replicated', 'Fully Replicated', 'Decision Tree Scalar'])#, loc="upper left", bbox_to_anchor=(1,1))
plt.title('Vectorized Speedups')
plt.savefig('writeup/figures/graphs/vector_speedups.png')
plt.close()


###########################
## PLOTTING CASE STUDIES ##
###########################
vals = [1 / csv_speedup(f'csvs/cases/matmul_3x3_case{i+1}.csv') for i in range(5)]
x = np.arange(len(vals)) * 0.75
plt.bar(x, vals,width=0.5, color='#41b6c4')
plt.xticks(x, ['Together', 'Separate', 'Rows/Cols', 'Cols/Rows', 'Individual'], rotation=20)
plt.ylabel('(Normalized) Speedup')
plt.axhline(1, color='red')
plt.title('Data Layout Case Study')
plt.savefig('writeup/figures/graphs/case_study.png')
plt.close()

####################
## PLOTTING TREES ##
####################

discs = {'100-100': 'Dense, Hom', '100-50': 'Dense, NonHom', '50-50': 'Sparse'}
labels = []
values = []
for disc in os.listdir('csvs/tree/'):
    labels.append(discs[disc])
    value = []
    for size in os.listdir(f'csvs/tree/{disc}'):
        if size not in ['5', '10']:
            continue
        speedups = np.array([1 / csv_speedup(f'csvs/tree/{disc}/{size}/{tree}') for tree in os.listdir(f'csvs/tree/{disc}/{size}')])
        print(f'{disc}.{size}:{speedups.mean()}')
        value.append(speedups.mean())

    values.append(tuple(value))

s10, s5 = zip(*values)
x = np.arange(len(labels))
plt.bar(x - width, s5, width=2 * width, color='#253494')
plt.bar(x + width, s10, width=2 * width, color='#2c7fb8')
plt.legend(['Depth 5', 'Depth 10'])
plt.xticks(x, labels)
plt.title('Random Polynomial Vectorized Speedups')
plt.axhline(1, color='red')
plt.ylabel('(Normalized) Speedup')
plt.savefig('writeup/figures/graphs/trees.png')
plt.close()


#######################
## PLOTTING SCHEDULE ##
#######################
schedule_10k = np.genfromtxt('csvs/dist10k.csv', delimiter=',')
schedule_15k = np.genfromtxt('csvs/dist15k.csv', delimiter=',')
schedule_20k = np.genfromtxt('csvs/dist20k.csv', delimiter=',')
# schedule_50k = np.genfromtxt('csvs/dist50k.csv', delimiter=',')


plt.plot(schedule_10k[1, :])
plt.plot(schedule_15k[1, :])
plt.plot(schedule_20k[1, :])
# plt.plot(schedule_50k[1, :])
plt.title('Schedule cost over time')
plt.xlabel('Number of rounds')
plt.ylabel('Cost')
plt.legend(['10k', '15k', '20k'])
plt.savefig('writeup/figures/graphs/schedules.png')