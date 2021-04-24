import z3
from typing import Dict, Set, List


def place_lanes(interstage: Dict[int, Set[int]], intrastage: Dict[int, List[int]]):

    opt = z3.Solver()

    num_instr = max(interstage[-1].keys()) + 1
    _lane = z3.IntVector('lane', num_instr)
    _arr = z3.IntVector('arr', num_instr)
    for instr in range(0, num_instr):
        opt.add(_lane[instr] >= 0)

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
