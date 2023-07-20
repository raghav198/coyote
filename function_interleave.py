from itertools import cycle
from coyote import *
from coyote.coyote_ast import Atom, Instr
from coyote.codegen import Schedule, codegen
from coyote.vectorize_circuit import CodeObject

import pickle 

class mapped_reg:
    def __init__(self, x: int, y: int):
        self.pre_val = x
        self.new_val = y
    def __repr__(self):
        return f'{self.pre_val}, {self.new_val}'

coyote = coyote_compiler()

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
expansion_size = 2
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

for step in sched_class_high.steps:
    if sched_class_high.instructions[step[0]].op == '*': # ideally this is the function call  
        for i in range(expansion_size):
            temp = step[i]
            for instr in instruc_low:
                dest_value = len_instr_low * (i) + instr.dest.val 
                if isinstance(instr.lhs, Atom) and isinstance(instr.lhs.val, int):
                    lhs_nw = int(instr.lhs.val) + len_instr_low * (i) 
                    rhs_nw = int(instr.rhs.val) + len_instr_low * (i) 
                    op_value = instr.op
                    new_instr.append(Instr(dest_value, Atom(lhs_nw), Atom(rhs_nw), op_value))
                else:
                    new_instr.append(Instr(dest_value, instr.lhs.val, instr.rhs.val, "~"))
            lanes_out_new = [(i+1) * l for l in lanes_out]
            lanes_out_interleaved = lanes_out_new[:]
            for x in range(expansion_size - 1):
                for k in lanes_out_new:
                    lanes_out_interleaved.append(k + x + 1) 
            align_out = sched[1].alignment
            align_out_interleaved = align_out * (i+1)
            temp_2 = ["_"] * 3
            
            temp_3 = [0]*10
            for x in sched_class_low.steps[len(sched_class_low.steps)-1]:
                temp_2[sched_class_low.lanes[x]] = sched_class_low.lanes[x ]
                temp_3[sched_class_low.lanes[x]] = x
  
            if i!=0: 
                for s in range(len(temp_3)):
                    temp_3[s] = temp_3[s] + len_instr_low
                    
            if temp not in new_dictionary:
                new_dictionary.setdefault(temp, [])
                for j in range(3):
                        if (j == temp_2[j]):
                            new_dictionary[temp].append(temp_3[j])
                        else:
                            new_dictionary[temp].append("_")
        new_schedule = Schedule(lanes_out_interleaved, align_out_interleaved, new_instr)

    else:
        length_z = len(new_instr) 
        for index,value in enumerate(step):
                if sched_class_high.instructions[value].lhs.val in new_dictionary:
                    for j,val in enumerate(new_dictionary[sched_class_high.instructions[value].lhs.val]):
                        if val != "_":
                            new_instr.append(Instr(length_z , Atom(val), Atom(new_dictionary[sched_class_high.instructions[value].rhs.val][j]), sched_class_high.instructions[step[0]].op))
                            print(j)
                            lanes_out_interleaved.append(2)
                            align_out_interleaved.append(len(new_schedule.steps))

new_schedule = Schedule(lanes_out_interleaved, align_out_interleaved, new_instr)
# pri(nt(lanes_out_interleaved, align_out_interleaved)
print(new_instr)
for i in new_schedule:
    print(i)

# # last_step = sched_class_high.steps[len( sched_class_high.steps)-1]
# after_function_call_expansion = []
# for i in last_step:
#     after_function_call_expansion.append(sched_class_high.instructions[i])

# for i in range(3):
#     for instr in after_function_call_expansion:
#         dest_value = len(new_instr) * (i) + instr.dest.val 
#         if isinstance(instr.lhs, Atom) and isinstance(instr.lhs.val, int):
#             lhs_nw = int(instr.lhs.val) + len_instr_low * (i) 
#             rhs_nw = int(instr.rhs.val) + len_instr_low * (i) 
#             op_value = instr.op
#             new_instr.append(Instr(dest_value, Atom(lhs_nw), Atom(rhs_nw), op_value))
#         else:
#             new_instr.append(Instr(dest_value, instr.lhs.val, instr.rhs.val, "~"))
#     # else:
# print(reg_dest)
# print(reg_left)
# print(reg_rhs)
# print(instr_sched)
# for i in instr_sched:
#     print(i)


# lanes_out_high = sched_high[1].lanes
# align_out_high = sched_high[1].alignment
# new_lanes = lanes_out_high[:]
# # x = [2 * l for l in new_lanes]
# # new_lanes = x[:]
# # for j in range(2):
# #     for k in x:
# #         new_lanes.append(k + 1 +j)
# # for i in range(len(lanes_out_high)): 
# #     x = [((lanes_out_high[i] + 1) * 2 + j * 2) for j in range(len(lanes_out_high)-1)]
# #     new_lanes = new_lanes + x
# new_lanes =  [0, 1, 0, 2,4,3,5,2,4]

# new_align = align_out_high[:]
# for i in range(len(align_out_high)):
#     y = [align_out_high[i] for j in range(len(align_out_high)-1)]
#     new_align = new_align + y
# dict_new = {}
# print(new_align)
# instr_new = sched_high[0][:]
# count = 0
# for instr in sched_high[0]:
#     # print(instr)
#     temp = instr.dest.val
#     for i in range(len(align_out_high) - 1):
#         dest_value = len(align_out_high) + instr.dest.val + i + count
#         if temp not in dict_new:
#             dict_new.setdefault(temp, [dest_value])
#         else:
#             dict_new[temp].append(dest_value)

#         if isinstance(instr.lhs, Atom) and isinstance(instr.lhs.val, int):
#             if int(instr.lhs.val) in dict_new:
#                 lhs_nw = dict_new[instr.lhs.val][i] 
#                 # print(lhs_nw)
#             if int(instr.rhs.val) in dict_new:
#                 rhs_nw =  dict_new[instr.rhs.val][i] 
#                 # print(rhs_nw)
#                 op_value = instr.op
#             instr_new.append(Instr(dest_value, Atom(lhs_nw), Atom(rhs_nw), op_value))
#         else:
#             instr_new.append(Instr(dest_value, Atom(instr.lhs.val), Atom(instr.rhs.val), instr.op))
    
#     count = count + 1

# print(instr_new)
# x = Schedule(new_lanes,new_align,instr_new)
# for i in x:
#     print(i)