from sys import stderr
import z3
from typing import Dict, Set, List
from ast_def import *
from vectorize import VecInstr
from itertools import combinations, groupby


def place_lanes(interstage: List[Dict[int, Set[int]]], intrastage: List[Dict[int, List[int]]], max_warp: int) -> List[int]:
    """DEPRECATED"""
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
    instr_lanes: List[int] = [0] * num_instr

    for d1 in interstage:
        for output in d1:
            instr_lanes[output] = lane_model[_lane[output]].as_long() # type: ignore

    for d2 in intrastage:
        for output, equiv_class in d2.items():
            for instr in equiv_class:
                instr_lanes[instr] = instr_lanes[output]

    return instr_lanes


def place_output_lanes(dependencies: List[Dict[int, Set[int]]], max_warp: int) -> Dict[int, int]:
    print(dependencies)
    """dependencies is a list of dictionaries that map an instruction tag (i.e. destination register) to the set of dependencies it consumes
    An invariant that must be maintained is that every element in a value must be a key from a previous dictionary in the list"""

    num_instr = max(sum((list(stage.keys()) for stage in dependencies), [])) + 1
    opt = z3.Solver()

    _lane = z3.IntVector('lane', num_instr)

    # bound each lane
    for i in range(num_instr):
        opt.add(_lane[i] < max_warp)
        opt.add(_lane[i] >= 0)

    
    # map each output to the stage its produced on
    stage_lookup: Dict[int, int] = {}
    for i, stage in enumerate(dependencies):
        for output in stage:
            stage_lookup[output] = i
    
    for stage in dependencies:
        # two outputs from the same stage cannot be on the same lane
        for o1, o2 in combinations(stage.keys(), 2):
            opt.assert_and_track(_lane[o1] != _lane[o2], f'lane{o1} != lane{o2}')

        # at least one producer <!--from each stage--> must be on the same lane as its consumer
        for output in stage:
            if len(stage[output]):
                opt.assert_and_track(z3.Or([_lane[output] == _lane[i] for i in stage[output]]), f'lane{output} in {stage[output]}')
        """for output in stage:
            # sort the dependencies by which stage their produced on
            all_producers = sorted(list(stage[output]), key=stage_lookup.__getitem__)
            # cluster them and loop through the clusters
            for _, stage_producers in groupby(all_producers, key=stage_lookup.__getitem__):
                stage_producers = list(stage_producers)
                opt.assert_and_track(z3.Or([_lane[i] == _lane[output] for i in stage_producers]), f'lane{output} in {stage_producers}')"""


    # opt.check()
    if opt.check() == z3.unsat:
        print(opt.unsat_core())
        raise SystemExit()
    lane_model = opt.model()
    output_lane_assignment: Dict[int, int] = {}
    
    for stage in dependencies:
        for output in stage:
            output_lane_assignment[output] = lane_model[_lane[output]].as_long() # type: ignore


    return output_lane_assignment



def propagate_lane_assigments(output_assignment: Dict[int, int], internal_deps: List[Dict[int, List[int]]]) -> List[int]:
    num_instr = max(output_assignment.keys()) + 1
    instr_lanes: List[int] = [0] * num_instr
    for out in output_assignment:
        instr_lanes[out] = output_assignment[out]

    for stage in internal_deps:
        for out in stage:
            for instr in stage[out]:
                instr_lanes[instr] = instr_lanes[out]

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
            reg = program[i].dest.val
            assert isinstance(reg, int)
            lane_num: int = lanes[reg]
            dest[lane_num] = reg
            lhs[lane_num] = program[i].lhs
            rhs[lane_num] = program[i].rhs

        vectorized_code.append(VecInstr(dest, lhs, rhs, program[instrs[0]].op))

    return vectorized_code


if __name__ == '__main__':
    deps: List[Dict[int, Set[int]]] = [{1: set(), 2: set()}, {3: set(), 4: set()}, {5: {1, 2, 3, 4}}]
    print(propagate_lane_assigments(place_output_lanes(deps, 6, 2), [{1: [0]}], 6))