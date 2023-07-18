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

coyote = coyote_compiler()

# Open the file to read the schedule
with open("code_object_dot3.pkl", "rb") as file:
    sched = pickle.load(file)
with open("code_object_dot6.pkl", "rb") as file_1:
    sched_high = pickle.load(file_1)
# print(sched_high[0])
instruc_low = sched[0]
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
align_out = sched[1].alignment

for step in sched_class_high.steps:
    if sched_class_high.instructions[step[0]].op == '*':
        reg_dest = step
        for j in step:
            reg_left.append([sched_class_high.instructions[j].lhs.val])
            reg_rhs.append([sched_class_high.instructions[j].rhs.val])

        for i in range(expansion_size):
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
        align_out_interleaved = align_out * 2
        instr_sched = Schedule(lanes_out_interleaved, align_out_interleaved, new_instr)

        reg_dest[i]    = instr_sched.steps[len(instr_sched.steps)-1]
    elif sched_class_high.instructions[step[0]].op == '+':
        pass

    elif sched_class_high.instructions[step[0]].op == '~':
        pass


print(reg_dest)
print(reg_left)
print(reg_rhs)
print(new_instr)
