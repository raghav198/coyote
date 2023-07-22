from itertools import cycle
from coyote import *
from coyote.coyote_ast import Atom, Instr
from coyote.codegen import Schedule, codegen
from coyote.vectorize_circuit import CodeObject

import pickle 

def add_length_instr(list_of_lists, constant):
    for i in range(len(list_of_lists)):
        for j in range(len(list_of_lists[i])):
            list_of_lists[i][j] += constant
    return list_of_lists

# Open the file to read the schedule
with open("code_object_dot3.pkl", "rb") as file:
    sched = pickle.load(file)
with open("code_object_dot6.pkl", "rb") as file_1:
    sched_high = pickle.load(file_1)
# print(sched_high[0])
instruc_low = sched[0]
sched_class_low = Schedule(sched[1].lanes,sched[1].alignment,sched[1])
len_instr_low = len(instruc_low) # length of a instruction
sched_class_high = Schedule(sched_high[1].lanes,sched_high[1].alignment,sched_high[0])
num_function_call = 2
input_expansion_size = 3
# duplicates the scalar instruction for a 2x2 schedule
new_instr = []
reg_map = {}
reg_high = 0
reg_dest = {}
reg_left = []
reg_rhs =[]
lanes_out = sched[1].lanes
# align_out = sched[1].alignment
# # reg_map = []
new_dictionary = {}

def max_length_of_list_of_lists(list_of_lists):
    max_length = 0

    for sublist in list_of_lists:
        if isinstance(sublist, list):
            sublist_length = len(sublist)
            if sublist_length > max_length:
                max_length = sublist_length

    return max_length

length_temp = max_length_of_list_of_lists(sched_class_low.steps)
length_upper = max_length_of_list_of_lists( sched_class_high.steps)

for step in sched_class_high.steps:
    if sched_class_high.instructions[step[0]].op == '*': # ideally this is the function call  
        # count = 0
        length_intsr = len(new_instr)
        for i in range(num_function_call):
            # if i > (len(step) - 1):
            #     count = 0
            temp = step[i]
            for instr in instruc_low:
                dest_value = len_instr_low * (i) + instr.dest.val + length_intsr
                if isinstance(instr.lhs, Atom) and isinstance(instr.lhs.val, int):
                    lhs_nw = int(instr.lhs.val) + len_instr_low * (i) 
                    rhs_nw = int(instr.rhs.val) + len_instr_low * (i) 
                    op_value = instr.op
                    new_instr.append(Instr(dest_value, Atom(lhs_nw), Atom(rhs_nw), op_value))
                else:
                    new_instr.append(Instr(dest_value, Atom(instr.lhs.val), Atom(instr.rhs.val), "~"))
            lanes_out_new = [(i+1) * l for l in lanes_out]
            lanes_out_interleaved = lanes_out_new[:]
            for x in range(num_function_call - 1):
                for k in lanes_out_new:
                    lanes_out_interleaved.append(k + x + 1) 
            align_out = sched[1].alignment
            align_out_interleaved = align_out * (i+1)
            reg_lane = ["_"] * length_temp
            reg_list = [0] * length_temp
            for x in sched_class_low.steps[len(sched_class_low.steps)-1]:
                reg_lane[sched_class_low.lanes[x]] = sched_class_low.lanes[x]
                reg_list[sched_class_low.lanes[x]] = x
  
            if i!=0: 
                for s in range(len(reg_list)):
                    reg_list[s] = reg_list[s] + len_instr_low * i
                    
            if temp not in new_dictionary:
                new_dictionary.setdefault(temp, [])
                for j in range(input_expansion_size):
                        if (j == reg_lane[j]):
                            new_dictionary[temp].append(reg_list[j])
                        else:
                            new_dictionary[temp].append("_")
    
            # count = count + 1
        new_schedule = Schedule(lanes_out_interleaved, align_out_interleaved, new_instr)
    else:
        step_size = len(new_schedule.steps)
        for index,value in enumerate(step):
            new_dictionary.setdefault(value, [])
            if sched_class_high.instructions[value].lhs.val in new_dictionary:
                for j,val in enumerate(new_dictionary[sched_class_high.instructions[value].lhs.val]):
                    if val != "_":
                        new_instr.append(Instr(len(new_instr) , Atom(val), Atom(new_dictionary[sched_class_high.instructions[value].rhs.val][j]), sched_class_high.instructions[step[0]].op))
                        if sched_class_high.lanes[value] == 0:
                            new_lane = length_upper * j 
                        else:
                            new_lane = length_upper * j + sched_class_high.lanes[value]
                        lanes_out_interleaved.append(new_lane)
                        new_dictionary[value].append(len(new_instr))
                        align_out_interleaved.append(step_size)
                    else:
                        new_dictionary[value].append(val)


# new_schedule = Schedule(lanes_out_interleaved, align_out_interleaved, new_instr)
# print(lanes_out_interleaved, align_out_interleaved)
# print(new_dictionary)
# print(new_instr)
# for i in new_schedule:
#     print(i)


for i in codegen(new_schedule):
    print(i)