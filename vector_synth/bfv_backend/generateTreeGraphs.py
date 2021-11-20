import sys 
import csv
import matplotlib
from matplotlib import pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
import scipy.stats as st
from matplotlib.pyplot import figure

folder = 'TreeData'

vec_enc1 = []
scal_enc1 = []
vec_run1 = []
scal_run1 = []
vec_enc2 = []
scal_enc2 = []
vec_run2 = []
scal_run2 = []
vec_enc3 = []
scal_enc3 = []
vec_run3 = []
scal_run3 = []
vec_enc4 = []
scal_enc4 = []
vec_run4 = []
scal_run4 = []
vec_enc5 = []
scal_enc5 = []
vec_run5 = []
scal_run5 = []
vec_enc6 = []
scal_enc6 = []
vec_run6 = []
scal_run6 = []

def average(list1):
    return (sum(list1) / len(list1))

with open(folder + '/tree50,50-3.csv') as file1:
    csv_reader = csv.reader(file1, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_enc1.append(int(row[1]))
            scal_enc1.append(int(row[5]))
            vec_run1.append(int(row[2]))
            scal_run1.append(int(row[6]))
            line_count += 1

with open(folder + '/tree50,50-6.csv') as file2:
    csv_reader = csv.reader(file2, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_enc2.append(int(row[1]))
            scal_enc2.append(int(row[5]))
            vec_run2.append(int(row[2]))
            scal_run2.append(int(row[6]))
            line_count += 1

with open(folder + '/tree100,50-3.csv') as file3:
    csv_reader = csv.reader(file3, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_enc3.append(int(row[1]))
            scal_enc3.append(int(row[5]))
            vec_run3.append(int(row[2]))
            scal_run3.append(int(row[6]))
            line_count += 1

with open(folder + '/tree100,50-6.csv') as file4:
    csv_reader = csv.reader(file4, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_enc4.append(int(row[1]))
            scal_enc4.append(int(row[5]))
            vec_run4.append(int(row[2]))
            scal_run4.append(int(row[6]))
            line_count += 1

with open(folder + '/tree100,100-3.csv') as file5:
    csv_reader = csv.reader(file5, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_enc5.append(int(row[1]))
            scal_enc5.append(int(row[5]))
            vec_run5.append(int(row[2]))
            scal_run5.append(int(row[6]))
            line_count += 1

with open(folder + '/tree100,100-6.csv') as file6:
    csv_reader = csv.reader(file6, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_enc6.append(int(row[1]))
            scal_enc6.append(int(row[5]))
            vec_run6.append(int(row[2]))
            scal_run6.append(int(row[6]))
            line_count += 1

tree50_50_3_vec_enc_avg = average(vec_enc1)
int1 = st.t.interval(alpha=0.95, df=len(vec_enc1)-1, loc=np.mean(vec_enc1), scale=st.sem(vec_enc1))
tree50_50_3_scal_enc_avg = average(scal_enc1)
int2 = st.t.interval(alpha=0.95, df=len(scal_enc1)-1, loc=np.mean(scal_enc1), scale=st.sem(scal_enc1))
tree50_50_3_vec_run_avg = average(vec_run1)
int3 = st.t.interval(alpha=0.95, df=len(vec_run1)-1, loc=np.mean(vec_run1), scale=st.sem(vec_run1))
tree50_50_3_scal_run_avg = average(scal_run1)
int4 = st.t.interval(alpha=0.95, df=len(scal_run1)-1, loc=np.mean(scal_run1), scale=st.sem(scal_run1))
tree50_50_6_vec_enc_avg = average(vec_enc2)
int5 = st.t.interval(alpha=0.95, df=len(vec_enc2)-1, loc=np.mean(vec_enc2), scale=st.sem(vec_enc2))
tree50_50_6_scal_enc_avg = average(scal_enc2)
int6 = st.t.interval(alpha=0.95, df=len(scal_enc2)-1, loc=np.mean(scal_enc2), scale=st.sem(scal_enc2))
tree50_50_6_vec_run_avg = average(vec_run2)
int7 = st.t.interval(alpha=0.95, df=len(vec_run2)-1, loc=np.mean(vec_run2), scale=st.sem(vec_run2))
tree50_50_6_scal_run_avg = average(scal_run2)
int8 = st.t.interval(alpha=0.95, df=len(scal_run2)-1, loc=np.mean(scal_run2), scale=st.sem(scal_run2))

tree100_50_3_vec_enc_avg = average(vec_enc3)
int9 = st.t.interval(alpha=0.95, df=len(vec_enc3)-1, loc=np.mean(vec_enc3), scale=st.sem(vec_enc3))
tree100_50_3_scal_enc_avg = average(scal_enc3)
int10 = st.t.interval(alpha=0.95, df=len(scal_enc3)-1, loc=np.mean(scal_enc3), scale=st.sem(scal_enc3))
tree100_50_3_vec_run_avg = average(vec_run3)
int11 = st.t.interval(alpha=0.95, df=len(vec_run3)-1, loc=np.mean(vec_run3), scale=st.sem(vec_run3))
tree100_50_3_scal_run_avg = average(scal_run3)
int12 = st.t.interval(alpha=0.95, df=len(scal_run3)-1, loc=np.mean(scal_run3), scale=st.sem(scal_run3))
tree100_50_6_vec_enc_avg = average(vec_enc4)
int13 = st.t.interval(alpha=0.95, df=len(vec_enc4)-1, loc=np.mean(vec_enc4), scale=st.sem(vec_enc4))
tree100_50_6_scal_enc_avg = average(scal_enc4)
int14 = st.t.interval(alpha=0.95, df=len(scal_enc4)-1, loc=np.mean(scal_enc4), scale=st.sem(scal_enc4))
tree100_50_6_vec_run_avg = average(vec_run4)
int15 = st.t.interval(alpha=0.95, df=len(vec_run4)-1, loc=np.mean(vec_run4), scale=st.sem(vec_run4))
tree100_50_6_scal_run_avg = average(scal_run4)
int16 = st.t.interval(alpha=0.95, df=len(scal_run4)-1, loc=np.mean(scal_run4), scale=st.sem(scal_run4))

tree100_100_3_vec_enc_avg = average(vec_enc5)
int17 = st.t.interval(alpha=0.95, df=len(vec_enc5)-1, loc=np.mean(vec_enc5), scale=st.sem(vec_enc5))
tree100_100_3_scal_enc_avg = average(scal_enc5)
int18 = st.t.interval(alpha=0.95, df=len(scal_enc5)-1, loc=np.mean(scal_enc5), scale=st.sem(scal_enc5))
tree100_100_3_vec_run_avg = average(vec_run5)
int19 = st.t.interval(alpha=0.95, df=len(vec_run5)-1, loc=np.mean(vec_run5), scale=st.sem(vec_run5))
tree100_100_3_scal_run_avg = average(scal_run5)
int20 = st.t.interval(alpha=0.95, df=len(scal_run5)-1, loc=np.mean(scal_run5), scale=st.sem(scal_run5))
tree100_100_6_vec_enc_avg = average(vec_enc6)
int21 = st.t.interval(alpha=0.95, df=len(vec_enc6)-1, loc=np.mean(vec_enc6), scale=st.sem(vec_enc6))
tree100_100_6_scal_enc_avg = average(scal_enc6)
int22 = st.t.interval(alpha=0.95, df=len(scal_enc6)-1, loc=np.mean(scal_enc6), scale=st.sem(scal_enc6))
tree100_100_6_vec_run_avg = average(vec_run6)
int23 = st.t.interval(alpha=0.95, df=len(vec_run6)-1, loc=np.mean(vec_run6), scale=st.sem(vec_run6))
tree100_100_6_scal_run_avg = average(scal_run6)
int24 = st.t.interval(alpha=0.95, df=len(scal_run6)-1, loc=np.mean(scal_run6), scale=st.sem(scal_run6))

figure(figsize=(10, 10), dpi=80)
norm_tree50_50_3_vec_enc = float(tree50_50_3_vec_enc_avg)/(tree50_50_3_scal_enc_avg + tree50_50_3_scal_run_avg)
norm_tree50_50_3_vec_run = float(tree50_50_3_vec_run_avg)/(tree50_50_3_scal_enc_avg + tree50_50_3_scal_run_avg)
plt.bar(1, norm_tree50_50_3_vec_run, color = 'green', yerr = (int3[1] - int3[0]) / (2 * (tree50_50_3_scal_enc_avg + tree50_50_3_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(1, norm_tree50_50_3_vec_enc, color = 'blue', yerr = (int1[1] - int1[0]) / (2 * (tree50_50_3_scal_enc_avg + tree50_50_3_scal_run_avg)), ecolor = 'black', bottom = norm_tree50_50_3_vec_run)

norm_tree50_50_3_scal_enc = float(tree50_50_3_scal_enc_avg)/(tree50_50_3_scal_enc_avg + tree50_50_3_scal_run_avg)
norm_tree50_50_3_scal_run = float(tree50_50_3_scal_run_avg)/(tree50_50_3_scal_enc_avg + tree50_50_3_scal_run_avg)
plt.bar(2, norm_tree50_50_3_scal_run, color = 'yellow', yerr = (int4[1] - int4[0]) / (2 * (tree50_50_3_scal_enc_avg + tree50_50_3_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(2, norm_tree50_50_3_scal_enc, color = 'red', yerr = (int2[1] - int2[0]) / (2 * (tree50_50_3_scal_enc_avg + tree50_50_3_scal_run_avg)), ecolor = 'black', bottom = norm_tree50_50_3_scal_run)

norm_tree50_50_6_vec_enc = float(tree50_50_6_vec_enc_avg)/(tree50_50_6_scal_enc_avg + tree50_50_6_scal_run_avg)
norm_tree50_50_6_vec_run = float(tree50_50_6_vec_run_avg)/(tree50_50_6_scal_enc_avg + tree50_50_6_scal_run_avg)
plt.bar(4, norm_tree50_50_6_vec_run, color = 'green', yerr = (int7[1] - int7[0]) / (2 * (tree50_50_6_scal_enc_avg + tree50_50_6_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(4, norm_tree50_50_6_vec_enc, color = 'blue', yerr = (int5[1] - int5[0]) / (2 * (tree50_50_6_scal_enc_avg + tree50_50_6_scal_run_avg)), ecolor = 'black', bottom = norm_tree50_50_6_vec_run)

norm_tree50_50_6_scal_enc = float(tree50_50_6_scal_enc_avg)/(tree50_50_6_scal_enc_avg + tree50_50_6_scal_run_avg)
norm_tree50_50_6_scal_run = float(tree50_50_6_scal_run_avg)/(tree50_50_6_scal_enc_avg + tree50_50_6_scal_run_avg)
plt.bar(5, norm_tree50_50_6_scal_run, color = 'yellow', yerr = (int8[1] - int8[0]) / (2 * (tree50_50_6_scal_enc_avg + tree50_50_6_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(5, norm_tree50_50_6_scal_enc, color = 'red', yerr = (int6[1] - int6[0]) / (2 * (tree50_50_6_scal_enc_avg + tree50_50_6_scal_run_avg)), ecolor = 'black', bottom = norm_tree50_50_6_scal_run)

norm_tree100_50_3_vec_enc = float(tree100_50_3_vec_enc_avg)/(tree100_50_3_scal_enc_avg + tree100_50_3_scal_run_avg)
norm_tree100_50_3_vec_run = float(tree100_50_3_vec_run_avg)/(tree100_50_3_scal_enc_avg + tree100_50_3_scal_run_avg)
plt.bar(7, norm_tree100_50_3_vec_run, color = 'green', yerr = (int11[1] - int11[0]) / (2 * (tree100_50_3_scal_enc_avg + tree100_50_3_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(7, norm_tree100_50_3_vec_enc, color = 'blue', yerr = (int9[1] - int9[0]) / (2 * (tree100_50_3_scal_enc_avg + tree100_50_3_scal_run_avg)), ecolor = 'black', bottom = norm_tree100_50_3_vec_run)

norm_tree100_50_3_scal_enc = float(tree100_50_3_scal_enc_avg)/(tree100_50_3_scal_enc_avg + tree100_50_3_scal_run_avg)
norm_tree100_50_3_scal_run = float(tree100_50_3_scal_run_avg)/(tree100_50_3_scal_enc_avg + tree100_50_3_scal_run_avg)
plt.bar(8, norm_tree100_50_3_scal_run, color = 'yellow', yerr = (int12[1] - int12[0]) / (2 * (tree100_50_3_scal_enc_avg + tree100_50_3_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(8, norm_tree100_50_3_scal_enc, color = 'red', yerr = (int10[1] - int10[0]) / (2 * (tree100_50_3_scal_enc_avg + tree100_50_3_scal_run_avg)), ecolor = 'black', bottom = norm_tree100_50_3_scal_run)

norm_tree100_50_6_vec_enc = float(tree100_50_6_vec_enc_avg)/(tree100_50_6_scal_enc_avg + tree100_50_6_scal_run_avg)
norm_tree100_50_6_vec_run = float(tree100_50_6_vec_run_avg)/(tree100_50_6_scal_enc_avg + tree100_50_6_scal_run_avg)
plt.bar(10, norm_tree100_50_6_vec_run, color = 'green', yerr = (int15[1] - int15[0]) / (2 * (tree100_50_6_scal_enc_avg + tree100_50_6_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(10, norm_tree100_50_6_vec_enc, color = 'blue', yerr = (int13[1] - int13[0]) / (2 * (tree100_50_6_scal_enc_avg + tree100_50_6_scal_run_avg)), ecolor = 'black', bottom = norm_tree100_50_6_vec_run)

norm_tree100_50_6_scal_enc = float(tree100_50_6_scal_enc_avg)/(tree100_50_6_scal_enc_avg + tree100_50_6_scal_run_avg)
norm_tree100_50_6_scal_run = float(tree100_50_6_scal_run_avg)/(tree100_50_6_scal_enc_avg + tree100_50_6_scal_run_avg)
plt.bar(11, norm_tree100_50_6_scal_run, color = 'yellow', yerr = (int16[1] - int16[0]) / (2 * (tree100_50_6_scal_enc_avg + tree100_50_6_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(11, norm_tree100_50_6_scal_enc, color = 'red', yerr = (int14[1] - int14[0]) / (2 * (tree100_50_6_scal_enc_avg + tree100_50_6_scal_run_avg)), ecolor = 'black', bottom = norm_tree100_50_6_scal_run)

norm_tree100_100_3_vec_enc = float(tree100_100_3_vec_enc_avg)/(tree100_100_3_scal_enc_avg + tree100_100_3_scal_run_avg)
norm_tree100_100_3_vec_run = float(tree100_100_3_vec_run_avg)/(tree100_100_3_scal_enc_avg + tree100_100_3_scal_run_avg)
plt.bar(13, norm_tree100_100_3_vec_run, color = 'green', yerr = (int19[1] - int19[0]) / (2 * (tree100_100_3_scal_enc_avg + tree100_100_3_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(13, norm_tree100_100_3_vec_enc, color = 'blue', yerr = (int17[1] - int17[0]) / (2 * (tree100_100_3_scal_enc_avg + tree100_100_3_scal_run_avg)), ecolor = 'black', bottom = norm_tree100_100_3_vec_run)

norm_tree100_100_3_scal_enc = float(tree100_100_3_scal_enc_avg)/(tree100_100_3_scal_enc_avg + tree100_100_3_scal_run_avg)
norm_tree100_100_3_scal_run = float(tree100_100_3_scal_run_avg)/(tree100_100_3_scal_enc_avg + tree100_100_3_scal_run_avg)
plt.bar(14, norm_tree100_100_3_scal_run, color = 'yellow', yerr = (int20[1] - int20[0]) / (2 * (tree100_100_3_scal_enc_avg + tree100_100_3_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(14, norm_tree100_100_3_scal_enc, color = 'red', yerr = (int18[1] - int18[0]) / (2 * (tree100_100_3_scal_enc_avg + tree100_100_3_scal_run_avg)), ecolor = 'black', bottom = norm_tree100_100_3_scal_run)

norm_tree100_100_6_vec_enc = float(tree100_100_6_vec_enc_avg)/(tree100_100_6_scal_enc_avg + tree100_100_6_scal_run_avg)
norm_tree100_100_6_vec_run = float(tree100_100_6_vec_run_avg)/(tree100_100_6_scal_enc_avg + tree100_100_6_scal_run_avg)
plt.bar(16, norm_tree100_100_6_vec_run, color = 'green', yerr = (int23[1] - int23[0]) / (2 * (tree100_100_6_scal_enc_avg + tree100_100_6_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(16, norm_tree100_100_6_vec_enc, color = 'blue', yerr = (int21[1] - int21[0]) / (2 * (tree100_100_6_scal_enc_avg + tree100_100_6_scal_run_avg)), ecolor = 'black', bottom = norm_tree100_100_6_vec_run)

norm_tree100_100_6_scal_enc = float(tree100_100_6_scal_enc_avg)/(tree100_100_6_scal_enc_avg + tree100_100_6_scal_run_avg)
norm_tree100_100_6_scal_run = float(tree100_100_6_scal_run_avg)/(tree100_100_6_scal_enc_avg + tree100_100_6_scal_run_avg)
plt.bar(17, norm_tree100_100_6_scal_run, color = 'yellow', yerr = (int24[1] - int24[0]) / (2 * (tree100_100_6_scal_enc_avg + tree100_100_6_scal_run_avg)), ecolor = 'black', label = 'scalar')
plt.bar(17, norm_tree100_100_6_scal_enc, color = 'red', yerr = (int22[1] - int22[0]) / (2 * (tree100_100_6_scal_enc_avg + tree100_100_6_scal_run_avg)), ecolor = 'black', bottom = norm_tree100_100_6_scal_run)

plt.xticks([1,4,7,10,13,16],["sparse_3", "sparse_6", "dense_nonhomogeneous_3", "dense_nonhomogeneous_6", "dense_homogeneous_3", "dense_homogeneous_6"], rotation = 25, fontsize = 10)
plt.show()