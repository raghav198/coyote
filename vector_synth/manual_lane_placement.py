from collections import defaultdict
from itertools import combinations
from typing import Dict, List, Set
import z3


def place_lanes_one_stage(dependencies: Dict[int, Set[int]], stage_outputs: List[Set[int]], opt: z3.Solver, lanes: Dict[int, z3.ArithRef]):
    consumers: Dict[int, int] = {}
    for output in dependencies:
        for producer in dependencies[output]:
            consumers[producer] = output

    all_inputs = set(consumers.keys())
    if len(all_inputs) == 0:
        return

    dependencies_per_stage: List[Dict[int, Set[int]]] = []
    for stage in stage_outputs:
        deps_from_cur_stage: Dict[int, Set[int]] = defaultdict(lambda: set())
        for dependency in stage.intersection(all_inputs):
            consumer = consumers[dependency]
            if consumer in deps_from_cur_stage:
                deps_from_cur_stage[consumer].add(dependency)
            else:
                deps_from_cur_stage[consumer] = set({dependency})
        dependencies_per_stage.append(deps_from_cur_stage)

    for output in dependencies:
        opt.assert_and_track(z3.Or([lanes[k] == lanes[output] for k in dependencies[output]]),
                             f'lanes[{output}] in {dependencies[output]}')

    for i in range(len(stage_outputs)):
        # most number of dependencies any output has from this particular stage
        n = max(len(dependencies_per_stage[i][out]) for out in dependencies)
        q = [z3.Int(f'q{j}_{i}') for j in range(n)]
        if len(q):
            opt.add(q[0] == 0)

        # for each producer from this stage
        for k in stage_outputs[i].intersection(all_inputs):
            # it has to be one of the 'n' possible shifts (one of which is 0)
            opt.assert_and_track(z3.Or([lanes[k] == (lanes[consumers[k]] + q[j])
                                        for j in range(n)]), f'lanes[{k}] == lanes[{consumers[k]}] + qj')


def place_lanes_manually(dependencies: List[Dict[int, Set[int]]], max_warp: int):
    print(f'{len(dependencies)} stages, {max_warp} lanes')
    print(dependencies)
    input()
    opt = z3.Solver()
    opt.set('timeout', 60 * 1000)
    lanes: Dict[int, z3.ArithRef] = {}

    stage_outputs = []

    for stage in dependencies:
        for output in stage:
            lanes[output] = z3.Int(f'lane({output})')
            opt.add(lanes[output] >= 0)
            opt.add(lanes[output] < max_warp)

        for out1, out2 in combinations(stage.keys(), 2):
            opt.assert_and_track(lanes[out1] != lanes[out2], f'lanes[{out1}] != lanes[{out2}]')

        place_lanes_one_stage(stage, stage_outputs, opt, lanes)
        stage_outputs.append(set(stage.keys()))

    lane_assignment: Dict[int, int] = {}

    ans = opt.check()

    if ans == z3.sat:
        for stage in dependencies:
            for output in stage:
                lane_assignment[output] = opt.model()[lanes[output]].as_long()
                # print(f'{output} -> {opt.model()[lanes[output]]}')
        return lane_assignment
    else:
        print('Retrying with more lanes...')
        print(opt.unsat_core())
        return place_lanes_manually(dependencies, max_warp + 5)
        raise SystemExit()


if __name__ == '__main__':
    dependencies = [
        {0: set(), 3: set(), 7: set(), 10: set(), 15: set(), 18: set(), 22: set(), 25: set()},
        {1: set(), 4: set(), 8: set(), 11: set(), 16: set(), 19: set(), 23: set(), 26: set()},
        {6: {0, 1, 3, 4}, 13: {8, 10, 11, 7}, 21: {16, 18, 19, 15}, 28: {25, 26, 22, 23}},
        {30: {21, 28, 13, 6}}]

    place_lanes_manually(dependencies, 8)
