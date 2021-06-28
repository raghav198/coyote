from sys import stderr
import z3
from typing import Dict, Set, List
from ast_def import *
from vectorize import VecInstr


def place_lanes(interstage: Dict[int, Set[int]], intrastage: Dict[int, List[int]], max_warp: int):

    opt = z3.Solver()

    num_instr = max(sum((list(stage.keys()) for stage in interstage), [])) + 1
    _lane = z3.IntVector('lane', num_instr)
    for instr in range(num_instr):
        opt.add(_lane[instr] >= 0)
        opt.add(_lane[instr] < max_warp)

    # Set up the || chain
    for stage_dict in interstage:
        for key in stage_dict.keys():
            opt.add(z3.And([_lane[key] != _lane[key1]
                            for key1 in stage_dict.keys() if key != key1]))
    for stage_dict in interstage[1:]:
        for key, val in stage_dict.items():
            opt.add(z3.Or([_lane[key] == _lane[i] for i in val]))

    opt.check()
    lane_model = opt.model()
    instr_lanes = [0] * num_instr

    for d in interstage:
        for output in d:
            instr_lanes[output] = lane_model[_lane[output]].as_long()

    for d in intrastage:
        for output, equiv_class in d.items():
            for instr in equiv_class:
                instr_lanes[instr] = instr_lanes[output]

    return instr_lanes


def build_vector_program(program: List[Instr],
                         lanes: List[int],
                         schedule: List[int]) -> List[VecInstr]:
    print('Building stage:', file=stderr)
    print('\n'.join(map(str, program)), file=stderr)
    vectorized_code = []
    warp = max(lanes) + 1

    # schedule  :: inst -> slot, inv_schedule :: slot -> [inst]
    inv_schedule = [[i for i in range(len(schedule)) if schedule[i] == slot]
                    for slot in set(schedule)]

    for instrs in inv_schedule:
        dest = [-1 for _ in range(warp)]
        lhs = [Atom(BLANK_SYMBOL) for _ in range(warp)]
        rhs = [Atom(BLANK_SYMBOL) for _ in range(warp)]

        for i in instrs:
            lane_num = lanes[program[i].dest.val]
            dest[lane_num] = program[i].dest.val
            lhs[lane_num] = program[i].lhs
            rhs[lane_num] = program[i].rhs

        vectorized_code.append(VecInstr(dest, lhs, rhs, program[i].op))

    return vectorized_code
