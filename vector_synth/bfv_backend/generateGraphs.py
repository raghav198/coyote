import sys 
import csv
import matplotlib
from matplotlib import pyplot as plt
import matplotlib.patches as mpatches
import numpy as np
import scipy.stats as st
from matplotlib.pyplot import figure

folder = 'DataUnreplicated'

vec_run1 = []
scal_run1 = []
vec_encrun1 = []
scal_encrun1 = []
vec_run2 = []
scal_run2 = []
vec_encrun2 = []
scal_encrun2 = []
vec_run3 = []
scal_run3 = []
vec_encrun3 = []
scal_encrun3 = []
vec_run4 = []
scal_run4 = []
vec_encrun4 = []
scal_encrun4 = []
vec_run5 = []
scal_run5 = []
vec_encrun5 = []
scal_encrun5 = []
vec_run6 = []
scal_run6 = []
vec_encrun6 = []
scal_encrun6 = []
vec_run7 = []
scal_run7 = []
vec_encrun7 = []
scal_encrun7 = []
vec_run8 = []
scal_run8 = []
vec_encrun8 = []
scal_encrun8 = []
vec_run9 = []
scal_run9 = []
vec_encrun9 = []
scal_encrun9 = []
vec_run10 = []
scal_run10 = []
vec_encrun10 = []
scal_encrun10 = []

def average(list1):
    return (sum(list1) / len(list1))

with open(folder + '/dot_product3x3.csv') as file1:
    csv_reader = csv.reader(file1, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run1.append(int(row[2]))
            scal_run1.append(int(row[6]))
            vec_encrun1.append(int(row[3]))
            scal_encrun1.append(int(row[7]))
            line_count += 1

with open(folder + '/dot_product6x6.csv') as file2:
    csv_reader = csv.reader(file2, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run2.append(int(row[2]))
            scal_run2.append(int(row[6]))
            vec_encrun2.append(int(row[3]))
            scal_encrun2.append(int(row[7]))
            line_count += 1

with open(folder + '/mat_convol4x4x2x2.csv') as file3:
    csv_reader = csv.reader(file3, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run3.append(int(row[2]))
            scal_run3.append(int(row[6]))
            vec_encrun3.append(int(row[3]))
            scal_encrun3.append(int(row[7]))
            line_count += 1

with open(folder + '/mat_convol4x4x3x3.csv') as file4:
    csv_reader = csv.reader(file4, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run4.append(int(row[2]))
            scal_run4.append(int(row[6]))
            vec_encrun4.append(int(row[3]))
            scal_encrun4.append(int(row[7]))
            line_count += 1

with open(folder + '/mat_mul_det2x2.csv') as file5:
    csv_reader = csv.reader(file5, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run5.append(int(row[2]))
            scal_run5.append(int(row[6]))
            vec_encrun5.append(int(row[3]))
            scal_encrun5.append(int(row[7]))
            line_count += 1

with open(folder + '/mat_mul_det3x3.csv') as file6:
    csv_reader = csv.reader(file6, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run6.append(int(row[2]))
            scal_run6.append(int(row[6]))
            vec_encrun6.append(int(row[3]))
            scal_encrun6.append(int(row[7]))
            line_count += 1

with open(folder + '/mat_mult2x2.csv') as file7:
    csv_reader = csv.reader(file7, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run7.append(int(row[2]))
            scal_run7.append(int(row[6]))
            vec_encrun7.append(int(row[3]))
            scal_encrun7.append(int(row[7]))
            line_count += 1

with open(folder + '/mat_mult3x3.csv') as file8:
    csv_reader = csv.reader(file8, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run8.append(int(row[2]))
            scal_run8.append(int(row[6]))
            vec_encrun8.append(int(row[3]))
            scal_encrun8.append(int(row[7]))
            line_count += 1

with open(folder + '/pairwise_dist2x2.csv') as file9:
    csv_reader = csv.reader(file9, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run9.append(int(row[2]))
            scal_run9.append(int(row[6]))
            vec_encrun9.append(int(row[3]))
            scal_encrun9.append(int(row[7]))
            line_count += 1

with open(folder + '/pairwise_dist3x3.csv') as file10:
    csv_reader = csv.reader(file10, delimiter=',')
    line_count = 0
    for row in csv_reader:
        if line_count == 0:
            line_count += 1
        else:
            vec_run10.append(int(row[2]))
            scal_run10.append(int(row[6]))
            vec_encrun10.append(int(row[3]))
            scal_encrun10.append(int(row[7]))
            line_count += 1

dp3x3_vec_encrun_avg = average(vec_encrun1)
int1 = st.t.interval(alpha=0.95, df=len(vec_encrun1)-1, loc=np.mean(vec_encrun1), scale=st.sem(vec_encrun1))
dp3x3_scal_encrun_avg = average(scal_encrun1)
int2 = st.t.interval(alpha=0.95, df=len(scal_encrun1)-1, loc=np.mean(scal_encrun1), scale=st.sem(scal_encrun1))
dp3x3_vec_run_avg = average(vec_run1)
int3 = st.t.interval(alpha=0.95, df=len(vec_run1)-1, loc=np.mean(vec_run1), scale=st.sem(vec_run1))
dp3x3_scal_run_avg = average(scal_run1)
int4 = st.t.interval(alpha=0.95, df=len(scal_run1)-1, loc=np.mean(scal_run1), scale=st.sem(scal_run1))
dp6x6_vec_encrun_avg = average(vec_encrun2)
int5 = st.t.interval(alpha=0.95, df=len(vec_encrun2)-1, loc=np.mean(vec_encrun2), scale=st.sem(vec_encrun2))
dp6x6_scal_encrun_avg = average(scal_encrun2)
int6 = st.t.interval(alpha=0.95, df=len(scal_encrun2)-1, loc=np.mean(scal_encrun2), scale=st.sem(scal_encrun2))
dp6x6_vec_run_avg = average(vec_run2)
int7 = st.t.interval(alpha=0.95, df=len(vec_run2)-1, loc=np.mean(vec_run2), scale=st.sem(vec_run2))
dp6x6_scal_run_avg = average(scal_run2)
int8 = st.t.interval(alpha=0.95, df=len(scal_run2)-1, loc=np.mean(scal_run2), scale=st.sem(scal_run2))
mc4x4x2x2_vec_encrun_avg = average(vec_encrun3)
int9 = st.t.interval(alpha=0.95, df=len(vec_encrun3)-1, loc=np.mean(vec_encrun3), scale=st.sem(vec_encrun3))
mc4x4x2x2_scal_encrun_avg = average(scal_encrun3)
int10 = st.t.interval(alpha=0.95, df=len(scal_encrun3)-1, loc=np.mean(scal_encrun3), scale=st.sem(scal_encrun3))
mc4x4x2x2_vec_run_avg = average(vec_run3)
int11 = st.t.interval(alpha=0.95, df=len(vec_run3)-1, loc=np.mean(vec_run3), scale=st.sem(vec_run3))
mc4x4x2x2_scal_run_avg = average(scal_run3)
int12 = st.t.interval(alpha=0.95, df=len(scal_run3)-1, loc=np.mean(scal_run3), scale=st.sem(scal_run3))
mc4x4x3x3_vec_encrun_avg = average(vec_encrun4)
int13 = st.t.interval(alpha=0.95, df=len(vec_encrun4)-1, loc=np.mean(vec_encrun4), scale=st.sem(vec_encrun4))
mc4x4x3x3_scal_encrun_avg = average(scal_encrun4)
int14 = st.t.interval(alpha=0.95, df=len(scal_encrun4)-1, loc=np.mean(scal_encrun4), scale=st.sem(scal_encrun4))
mc4x4x3x3_vec_run_avg = average(vec_run4)
int15 = st.t.interval(alpha=0.95, df=len(vec_run4)-1, loc=np.mean(vec_run4), scale=st.sem(vec_run4))
mc4x4x3x3_scal_run_avg = average(scal_run4)
int16 = st.t.interval(alpha=0.95, df=len(scal_run4)-1, loc=np.mean(scal_run4), scale=st.sem(scal_run4))
mmd2x2_vec_encrun_avg = average(vec_encrun5)
int17 = st.t.interval(alpha=0.95, df=len(vec_encrun5)-1, loc=np.mean(vec_encrun5), scale=st.sem(vec_encrun5))
mmd2x2_scal_encrun_avg = average(scal_encrun5)
int18 = st.t.interval(alpha=0.95, df=len(scal_encrun5)-1, loc=np.mean(scal_encrun5), scale=st.sem(scal_encrun5))
mmd2x2_vec_run_avg = average(vec_run5)
int19 = st.t.interval(alpha=0.95, df=len(vec_run5)-1, loc=np.mean(vec_run5), scale=st.sem(vec_run5))
mmd2x2_scal_run_avg = average(scal_run5)
int20 = st.t.interval(alpha=0.95, df=len(scal_run5)-1, loc=np.mean(scal_run5), scale=st.sem(scal_run5))
mmd3x3_vec_encrun_avg = average(vec_encrun6)
int21 = st.t.interval(alpha=0.95, df=len(vec_encrun6)-1, loc=np.mean(vec_encrun6), scale=st.sem(vec_encrun6))
mmd3x3_scal_encrun_avg = average(scal_encrun6)
int22 = st.t.interval(alpha=0.95, df=len(scal_encrun6)-1, loc=np.mean(scal_encrun6), scale=st.sem(scal_encrun6))
mmd3x3_vec_run_avg = average(vec_run6)
int23 = st.t.interval(alpha=0.95, df=len(vec_run6)-1, loc=np.mean(vec_run6), scale=st.sem(vec_run6))
mmd3x3_scal_run_avg = average(scal_run6)
int24 = st.t.interval(alpha=0.95, df=len(scal_run6)-1, loc=np.mean(scal_run6), scale=st.sem(scal_run6))
mm2x2_vec_encrun_avg = average(vec_encrun7)
int25 = st.t.interval(alpha=0.95, df=len(vec_encrun7)-1, loc=np.mean(vec_encrun7), scale=st.sem(vec_encrun7))
mm2x2_scal_encrun_avg = average(scal_encrun7)
int26 = st.t.interval(alpha=0.95, df=len(scal_encrun7)-1, loc=np.mean(scal_encrun7), scale=st.sem(scal_encrun7))
mm2x2_vec_run_avg = average(vec_run7)
int27 = st.t.interval(alpha=0.95, df=len(vec_run7)-1, loc=np.mean(vec_run7), scale=st.sem(vec_run7))
mm2x2_scal_run_avg = average(scal_run7)
int28 = st.t.interval(alpha=0.95, df=len(scal_run7)-1, loc=np.mean(scal_run7), scale=st.sem(scal_run7))
mm3x3_vec_encrun_avg = average(vec_encrun8)
int29 = st.t.interval(alpha=0.95, df=len(vec_encrun8)-1, loc=np.mean(vec_encrun8), scale=st.sem(vec_encrun8))
mm3x3_scal_encrun_avg = average(scal_encrun8)
int30 = st.t.interval(alpha=0.95, df=len(scal_encrun8)-1, loc=np.mean(scal_encrun8), scale=st.sem(scal_encrun8))
mm3x3_vec_run_avg = average(vec_run8)
int31 = st.t.interval(alpha=0.95, df=len(vec_run8)-1, loc=np.mean(vec_run8), scale=st.sem(vec_run8))
mm3x3_scal_run_avg = average(scal_run8)
int32 = st.t.interval(alpha=0.95, df=len(scal_run8)-1, loc=np.mean(scal_run8), scale=st.sem(scal_run8))
pd2x2_vec_encrun_avg = average(vec_encrun9)
int33 = st.t.interval(alpha=0.95, df=len(vec_encrun9)-1, loc=np.mean(vec_encrun9), scale=st.sem(vec_encrun9))
pd2x2_scal_encrun_avg = average(scal_encrun9)
int34 = st.t.interval(alpha=0.95, df=len(scal_encrun9)-1, loc=np.mean(scal_encrun9), scale=st.sem(scal_encrun9))
pd2x2_vec_run_avg = average(vec_run9)
int35 = st.t.interval(alpha=0.95, df=len(vec_run9)-1, loc=np.mean(vec_run9), scale=st.sem(vec_run9))
pd2x2_scal_run_avg = average(scal_run9)
int36 = st.t.interval(alpha=0.95, df=len(scal_run9)-1, loc=np.mean(scal_run9), scale=st.sem(scal_run9))
pd3x3_vec_encrun_avg = average(vec_encrun10)
int37 = st.t.interval(alpha=0.95, df=len(vec_encrun10)-1, loc=np.mean(vec_encrun10), scale=st.sem(vec_encrun10))
pd3x3_scal_encrun_avg = average(scal_encrun10)
int38 = st.t.interval(alpha=0.95, df=len(scal_encrun10)-1, loc=np.mean(scal_encrun10), scale=st.sem(scal_encrun10))
pd3x3_vec_run_avg = average(vec_run10)
int39 = st.t.interval(alpha=0.95, df=len(vec_run10)-1, loc=np.mean(vec_run10), scale=st.sem(vec_run10))
pd3x3_scal_run_avg = average(scal_run10)
int40 = st.t.interval(alpha=0.95, df=len(scal_run10)-1, loc=np.mean(scal_run10), scale=st.sem(scal_run10))

figure(figsize=(10, 10), dpi=80)
plt.bar(1, height = float(dp3x3_vec_encrun_avg)/dp3x3_scal_encrun_avg, color = 'blue', yerr = (int1[1] - int1[0]) / (2 * dp3x3_scal_encrun_avg), ecolor = 'black', label = 'vector')
plt.bar(2, height = 1, color = 'red', yerr = (int2[1] - int2[0]) / (2 * dp3x3_scal_encrun_avg), ecolor = 'black', label = 'scalar')

plt.bar(4, height = float(dp6x6_vec_encrun_avg)/dp6x6_scal_encrun_avg, color = 'blue', yerr = (int5[1] - int5[0]) / (2 * dp6x6_scal_encrun_avg), ecolor = 'black')
plt.bar(5, height = 1, color = 'red', yerr = (int6[1] - int6[0]) / (2 * dp6x6_scal_encrun_avg), ecolor = 'black')

plt.bar(7, height = float(mc4x4x2x2_vec_encrun_avg)/mc4x4x2x2_scal_encrun_avg, color = 'blue', yerr = (int9[1] - int9[0]) / (2 * mc4x4x2x2_scal_encrun_avg), ecolor = 'black')
plt.bar(8, height = 1, color = 'red', yerr = (int10[1] - int10[0]) / (2 * mc4x4x2x2_scal_encrun_avg), ecolor = 'black')

plt.bar(10, height = float(mc4x4x3x3_vec_encrun_avg)/mc4x4x3x3_scal_encrun_avg, color = 'blue', yerr = (int13[1] - int13[0]) / (2 * mc4x4x3x3_scal_encrun_avg), ecolor = 'black')
plt.bar(11, height = 1, color = 'red', yerr = (int14[1] - int14[0]) / (2 * mc4x4x3x3_scal_encrun_avg), ecolor = 'black')

plt.bar(13, height = float(mmd2x2_vec_encrun_avg)/mmd2x2_scal_encrun_avg, color = 'blue', yerr = (int17[1] - int17[0]) / (2 * mmd2x2_scal_encrun_avg), ecolor = 'black')
plt.bar(14, height = 1, color = 'red', yerr = (int18[1] - int18[0]) / (2 * mmd2x2_scal_encrun_avg), ecolor = 'black')

plt.bar(16, height = float(mmd3x3_vec_encrun_avg)/mmd3x3_scal_encrun_avg, color = 'blue', yerr = (int21[1] - int21[0]) / (2 * mmd3x3_scal_encrun_avg), ecolor = 'black')
plt.bar(17, height = 1, color = 'red', yerr = (int22[1] - int22[0]) / (2 * mmd3x3_scal_encrun_avg), ecolor = 'black')

plt.bar(19, height = float(mm2x2_vec_encrun_avg)/mm2x2_scal_encrun_avg, color = 'blue', yerr = (int25[1] - int25[0]) / (2 * mm2x2_scal_encrun_avg), ecolor = 'black')
plt.bar(20, height = 1, color = 'red', yerr = (int26[1] - int26[0]) / (2 * mm2x2_scal_encrun_avg), ecolor = 'black')

plt.bar(22, height = float(mm3x3_vec_encrun_avg)/mm3x3_scal_encrun_avg, color = 'blue', yerr = (int29[1] - int29[0]) / (2 * mm3x3_scal_encrun_avg), ecolor = 'black')
plt.bar(23, height = 1, color = 'red', yerr = (int30[1] - int30[0]) / (2 * mm3x3_scal_encrun_avg), ecolor = 'black')

plt.bar(25, height = float(pd2x2_vec_encrun_avg)/pd2x2_scal_encrun_avg, color = 'blue', yerr = (int33[1] - int33[0]) / (2 * pd2x2_scal_encrun_avg), ecolor = 'black')
plt.bar(26, height = 1, color = 'red', yerr = (int34[1] - int34[0]) / (2 * pd2x2_scal_encrun_avg), ecolor = 'black')

plt.bar(28, height = float(pd3x3_vec_encrun_avg)/pd3x3_scal_encrun_avg, color = 'blue', yerr = (int37[1] - int37[0]) / (2 * pd3x3_scal_encrun_avg), ecolor = 'black')
plt.bar(29, height = 1, color = 'red', yerr = (int38[1] - int38[0]) / (2 * pd3x3_scal_encrun_avg), ecolor = 'black')
ax = plt.gca()
plt.xticks([1,4,7,10,13,16,19,22,25,28],["dot_prod3x3", "dot_prod6x6", "mat_convol4x4x2x2", "mat_convol4x4x3x3", "mat_mul_det2x2", "mat_mul_det3x3", "mat_mul2x2", "mat_mul3x3", "pairwise_dist2x2", "pairwise_dist3x3"], rotation = 35, fontsize = 10)
#leg = ax.legend(loc = 'upper left')
plt.show()

figure(figsize=(10, 10), dpi=80)
plt.bar(1, height = float(dp3x3_vec_run_avg)/dp3x3_scal_run_avg, color = 'blue', yerr = (int3[1] - int3[0]) / (2 * dp3x3_scal_run_avg), ecolor = 'black', label = 'vector')
plt.bar(2, height = 1, color = 'red', yerr = (int4[1] - int4[0]) / (2 * dp3x3_scal_run_avg), ecolor = 'black', label = 'scalar')

plt.bar(4, height = float(dp6x6_vec_run_avg)/dp6x6_scal_run_avg, color = 'blue', yerr = (int7[1] - int7[0]) / (2 * dp6x6_scal_run_avg), ecolor = 'black')
plt.bar(5, height = 1, color = 'red', yerr = (int8[1] - int8[0]) / (2 * dp6x6_scal_run_avg), ecolor = 'black')

plt.bar(7, height = float(mc4x4x2x2_vec_run_avg)/mc4x4x2x2_scal_run_avg, color = 'blue', yerr = (int11[1] - int11[0]) / (2 * mc4x4x2x2_scal_run_avg), ecolor = 'black')
plt.bar(8, height = 1, color = 'red', yerr = (int12[1] - int12[0]) / (2 * mc4x4x2x2_scal_run_avg), ecolor = 'black')

plt.bar(10, height = float(mc4x4x3x3_vec_run_avg)/mc4x4x3x3_scal_run_avg, color = 'blue', yerr = (int15[1] - int15[0]) / (2 * mc4x4x3x3_scal_run_avg), ecolor = 'black')
plt.bar(11, height = 1, color = 'red', yerr = (int16[1] - int16[0]) / (2 * mc4x4x3x3_scal_run_avg), ecolor = 'black')

plt.bar(13, height = float(mmd2x2_vec_run_avg)/mmd2x2_scal_run_avg, color = 'blue', yerr = (int19[1] - int19[0]) / (2 * mmd2x2_scal_run_avg), ecolor = 'black')
plt.bar(14, height = 1, color = 'red', yerr = (int20[1] - int20[0]) / (2 * mmd2x2_scal_run_avg), ecolor = 'black')

plt.bar(16, height = float(mmd3x3_vec_run_avg)/mmd3x3_scal_run_avg, color = 'blue', yerr = (int23[1] - int23[0]) / (2 * mmd3x3_scal_run_avg), ecolor = 'black')
plt.bar(17, height = 1, color = 'red', yerr = (int24[1] - int24[0]) / (2 * mmd3x3_scal_run_avg), ecolor = 'black')

plt.bar(19, height = float(mm2x2_vec_run_avg)/mm2x2_scal_run_avg, color = 'blue', yerr = (int27[1] - int27[0]) / (2 * mm2x2_scal_run_avg), ecolor = 'black')
plt.bar(20, height = 1, color = 'red', yerr = (int28[1] - int28[0]) / (2 * mm2x2_scal_run_avg), ecolor = 'black')

plt.bar(22, height = float(mm3x3_vec_run_avg)/mm3x3_scal_run_avg, color = 'blue', yerr = (int31[1] - int31[0]) / (2 * mm3x3_scal_run_avg), ecolor = 'black')
plt.bar(23, height = 1, color = 'red', yerr = (int32[1] - int32[0]) / (2 * mm3x3_scal_run_avg), ecolor = 'black')

plt.bar(25, height = float(pd2x2_vec_run_avg)/pd2x2_scal_run_avg, color = 'blue', yerr = (int35[1] - int35[0]) / (2 * pd2x2_scal_run_avg), ecolor = 'black')
plt.bar(26, height = 1, color = 'red', yerr = (int36[1] - int36[0]) / (2 * pd2x2_scal_run_avg), ecolor = 'black')

plt.bar(28, height = float(pd3x3_vec_run_avg)/pd3x3_scal_run_avg, color = 'blue', yerr = (int39[1] - int39[0]) / (2 * pd3x3_scal_run_avg), ecolor = 'black')
plt.bar(29, height = 1, color = 'red', yerr = (int40[1] - int40[0]) / (2 * pd3x3_scal_run_avg), ecolor = 'black')
ax = plt.gca()
plt.xticks([1,4,7,10,13,16,19,22,25,28],["dot_prod3x3", "dot_prod6x6", "mat_convol4x4x2x2", "mat_convol4x4x3x3", "mat_mul_det2x2", "mat_mul_det3x3", "mat_mul2x2", "mat_mul3x3", "pairwise_dist2x2", "pairwise_dist3x3"], rotation = 35, fontsize = 10)
#leg = ax.legend(loc = 'upper left')
plt.show()