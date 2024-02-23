from itertools import cycle
from coyote import *
from coyote.coyote_ast import Atom, Instr
from coyote.codegen import Schedule, codegen
from coyote.vectorize_circuit import CodeObject
import pickle 
from itertools import groupby

# Open the file to read the schedule
with open("code_object_dot3.pkl", "rb") as file:
    inner = pickle.load(file) # inner schedule
with open("code_object_dot6.pkl", "rb") as file_1:
    outer = pickle.load(file_1) # outer schedule

class Interleave:
    def __init__(self, inner, outer, expansion_size):
        self.sched_inner_instr = inner[0]         # The inner schedule instructions
        self.sched_inner = Schedule(inner[1].lanes, inner[1].alignment, self.sched_inner_instr)         # The inner schedule
        self.instr_inner_len = len(self.sched_inner_instr)         # Length of the inner schedule instruction
        self.sched_outer = Schedule(outer[1].lanes, outer[1].alignment, outer[0])         # The outer schedule
        self.expansion_size = expansion_size          # Expansion size (assuming this might be used somewhere within the class)
        self.instr_interleave = []
        self.lanes_inner = inner[1].lanes
        self.lanes_outer = outer[1].lanes
        self.lanes_interleave = []
        self.alignment_inner =  inner[1].alignment
        self.alignment_interleave = []
        self.empty_reg = ["_"]
        self.inner_sched_len = self.reg_len(self.sched_inner.steps)
        self.outer_sched_len = self.reg_len(self.sched_outer.steps)
        self.expand_reg_lane = ["_"] * self.inner_sched_len
        self.expand_reg_num = [0]  * self.inner_sched_len
        self.expand_reg_dic = {}
        self.interleave()



    def interleave(self):
        for step in self.sched_outer.steps:
            if self.sched_outer.instructions[step[0]].op == '*': # parallelizing multiple multiplications
                for itr in range(self.expansion_size):
                    for instr in self.sched_inner_instr:
                        dest_reg =  self.instr_inner_len * (itr) + instr.dest.val 
                        if isinstance(instr.lhs, Atom) and isinstance(instr.lhs.val, int):
                            lhs_reg = int(instr.lhs.val) +  self.instr_inner_len * (itr) 
                            rhs_reg = int(instr.rhs.val) +  self.instr_inner_len * (itr) 
                            op_instr = instr.op
                            self.instr_interleave.append(Instr(dest_reg, Atom(lhs_reg), Atom(rhs_reg), op_instr))
                        else:
                            self.instr_interleave.append(Instr(dest_reg, instr.lhs.val, instr.rhs.val, "~"))
                    for x in self.sched_inner.steps[len(self.sched_inner.steps)-1]:
                        self.expand_reg_lane[self.sched_inner.lanes[x]] = self.sched_inner.lanes[x]
                        self.expand_reg_num[self.sched_inner.lanes[x]] = x
                    if itr > 0: 
                        for i, reg in enumerate(self.expand_reg_num):
                            if reg > 0:       
                                self.expand_reg_num[i] = reg + self.instr_inner_len  * itr

                    self.expand_reg_dic.setdefault(step[itr], [])
                    for i in range(self.inner_sched_len):
                            if isinstance(self.expand_reg_lane[i], int):
                                self.expand_reg_dic[step[itr]].append(self.expand_reg_num[i])
                            else:
                                self.expand_reg_dic[step[itr]].append("_")
               
                    # self.lanes_interleave = self.lane()
                    temp_lane = [(itr+1) * l for l in self.lanes_inner]
                    self.lanes_interleave = temp_lane[:]
                    for x in range(self.expansion_size - 1):
                        for k in  self.lanes_inner:
                            self.lanes_interleave.append(k + x + 1) 
                    self.alignment_interleave = self.alignment_inner * (itr + 1)
                intermediate_schedule = Schedule(self.lanes_interleave, self.alignment_interleave, self.instr_interleave)
                for i in intermediate_schedule:
                    print(i)
            else:
                intermediate_sche_len = len(intermediate_schedule.steps)
                for i,reg_o in enumerate(step):
                    self.expand_reg_dic.setdefault(reg_o, [])
                    if self.sched_outer.instructions[reg_o].lhs.val in self.expand_reg_dic:
                        for j,reg_i in enumerate(self.expand_reg_dic[self.sched_outer.instructions[reg_o].lhs.val]):
                            if isinstance(self.expand_reg_lane[i], int):
                                self.instr_interleave.append(Instr(len(self.instr_interleave) , Atom(reg_i), Atom(self.expand_reg_dic[self.sched_outer.instructions[reg_i].rhs.val][j]), self.sched_outer.instructions[step[0]].op))
                                if self.sched_outer.lanes[reg] > 0:
                                    new_lane = self.outer_sched_len * j 
                                else:
                                    new_lane = self.outer_sched_len * j + self.lanes_outer[reg_o]
                                self.lanes_interleave.append(new_lane)
                                self.expand_reg_dic[reg_o].append(len(self.instr_interleave))
                                self.alignment_interleave.append(intermediate_sche_len)
                            else:
                                self.expand_reg_dic[reg_o].append(reg_i)



    def reg_len(self, para):
        max_length = 0
        for sublist in para:
            if isinstance(sublist, list):
                sublist_length = len(sublist)
                if sublist_length > max_length:
                    max_length = sublist_length

        return max_length

Interleaved = Interleave(inner, outer, 2)

Interleaved_schedule = Schedule( Interleaved.lanes_interleave,  Interleaved.alignment_interleave, Interleaved.instr_interleave)
for i in Interleaved_schedule:
    print(i)