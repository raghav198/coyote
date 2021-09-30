from collections import defaultdict
from itertools import combinations
from typing import Dict, List, Set, Tuple
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
                                        for j in range(n)]), f'lanes[{k}] == lanes[{consumers[k]}] + q{{0..{n}}}')


def place_lanes_manually(dependencies: List[Dict[int, Set[int]]], max_warp: int, givens: Dict[int, int] = {}, offset=0):
    print(f'{len(dependencies)} stages, {max_warp} lanes')
    # print(dependencies)
    # print(givens)
    # raise SystemExit()
    opt = z3.Solver()
    opt.set('timeout', 30 * 1000)
    lanes: Dict[int, z3.ArithRef] = {}

    stage_outputs = []

    for stage in dependencies:
        for output in stage:
            lanes[output] = z3.Int(f'lane({output})')
            opt.add(lanes[output] >= 0)
            opt.assert_and_track(lanes[output] < max_warp, f'lanes[{output}] < {max_warp}')

        if not set(stage.keys()).isdisjoint(givens.keys()):
            # this stage has been computed already based on the givens passed in
            continue

        for out1, out2 in combinations(stage.keys(), 2):
            opt.assert_and_track(lanes[out1] != lanes[out2], f'lanes[{out1}] != lanes[{out2}]')

        place_lanes_one_stage(stage, stage_outputs, opt, lanes)
        stage_outputs.append(set(stage.keys()))


    for lane in givens:
        opt.add(lanes[lane] == givens[lane])
    lane_assignment: Dict[int, int] = {}

    ans = opt.check()

    if ans == z3.sat:
        for stage in dependencies:
            for output in stage:
                lane_assignment[output] = opt.model()[lanes[output]].as_long() + offset
                # print(f'{output} -> {opt.model()[lanes[output]]}')
        return lane_assignment
    else:
        # print('Retrying with more lanes...')
        print(opt.unsat_core())
        print('FAILED')
        # return place_lanes_manually(dependencies, max_warp + 5)
        # raise SystemExit()

def compute_closure(deps, key):
    for dep_dict in deps:
        if key not in dep_dict:
            continue
        ans: Set = dep_dict[key].copy()
        for key2 in ans.copy():
            ans.update(compute_closure(deps, key2))

        return ans

def merge_classes(sets: Dict[int, Set[int]]):
    groups = set(sets.keys())
    equiv_classes: Dict[int, Set[int]] = {}
    for group in groups:
        equiv_classes[group] = {group}

    def combine(equiv_classes: Dict[int, Set[int]], g1: int, g2: int):
        union = equiv_classes[g1].union(equiv_classes[g2])
        equiv_classes[g1] = union
        equiv_classes[g2] = union

    for g1, g2 in combinations(groups, 2):
        if not sets[g1].isdisjoint(sets[g2]):
            combine(equiv_classes, g1, g2)

    return list(equiv_classes.values())

def restrict(stages: List[Dict[int, Set[int]]], outputs: Set[int]):
    new_stages: List[Dict[int, Set[int]]] = []
    for stage in stages:
        new_stage = {key: val for key, val in stage.items() if key in outputs}
        new_stages.append(new_stage)
    while len(new_stages[-1]) == 0:
        del new_stages[-1]
    return new_stages


def place_lanes_piecewise(dependencies: List[Dict[int, Set[int]]], max_warp: int, givens: Dict[int, int] = {}):
    heights: Dict[int, int] = defaultdict(int)
    stage_heights = []
    for stage in dependencies:
        for key in stage:
            heights[key] = max((heights[inp] for inp in stage[key]), default=0) + 1
        stage_heights.append(max(heights[v] for v in stage.keys()))

    for num_stages in range(len(dependencies), 1, -1):
        print(num_stages)
        stages = dependencies[:num_stages].copy()
        print(len(stages))
        closures: Dict[int, Set[int]] = {}
        for key in stages[-1]:
            closures[key] = compute_closure(stages, key)

        
        if sum(map(len, closures.values())) == 0:
            break

        classes = merge_classes(closures)
        print('missing: ', set(dependencies[0].keys()) - set().union(*(closures.values())))
        placements = []
        offset = 0
        for toplevels in classes:
            print(f'{toplevels} / {classes}')
            all_outputs = set().union(*(closures[top] for top in toplevels)).union(toplevels)
            
            restricted_stages = restrict(stages, all_outputs)
            # print(stages)
            # print(restricted_stages)
            # raise SystemExit()
            print('max len: ', max(map(len, restricted_stages)))
            placement = place_lanes_manually(restricted_stages, max(map(len, restricted_stages)), givens=givens, offset=offset)
            offset += max(map(len, restricted_stages))
            if placement is None:
                break
            placements.append(placement)
        else:
            print(f'ALL SUCCESSFUL!')
            break
    
    already_defined = dict()
    for stage_placement in placements:
        already_defined.update(stage_placement)

    if num_stages == len(dependencies):
        return already_defined

    final_answer = place_lanes_piecewise(dependencies, max_warp, givens=already_defined)
    return final_answer


if __name__ == '__main__':
    # dependencies = [
    #     {0: set(), 3: set(), 7: set(), 10: set(), 15: set(), 18: set(), 22: set(), 25: set()},
    #     {1: set(), 4: set(), 8: set(), 11: set(), 16: set(), 19: set(), 23: set(), 26: set()},
    #     {6: {0, 1, 3, 4}, 13: {8, 10, 11, 7}, 21: {16, 18, 19, 15}, 28: {25, 26, 22, 23}},
    #     {30: {21, 28, 13, 6}}]

    dependencies = [{0: set(), 3: set(), 6: set(), 11: set(), 14: set(), 17: set(), 22: set(), 25: set(), 28: set(), 34: set(), 37: set(), 40: set(), 45: set(), 48: set(), 51: set(), 59: set(), 62: set(), 65: set(), 70: set(), 73: set(), 76: set(), 81: set(), 84: set(), 87: set(), 93: set(), 96: set(), 99: set(), 104: set(), 107: set(), 110: set(), 118: set(), 121: set(), 124: set(), 129: set(), 132: set(), 135: set(), 140: set(), 143: set(), 146: set(), 152: set(), 155: set(), 158: set(), 163: set(), 166: set(), 169: set()}, {1: set(), 4: set(), 7: set(), 12: set(), 15: set(), 18: set(), 23: set(), 26: set(), 29: set(), 35: set(), 38: set(), 41: set(), 46: set(), 49: set(), 52: set(), 60: set(), 63: set(), 66: set(), 71: set(), 74: set(), 77: set(), 82: set(), 85: set(), 88: set(), 94: set(), 97: set(), 100: set(), 105: set(), 108: set(), 111: set(), 119: set(), 122: set(), 125: set(), 130: set(), 133: set(), 136: set(), 141: set(), 144: set(), 147: set(), 153: set(), 156: set(), 159: set(), 164: set(), 167: set(), 170: set()}, {10: {0, 1, 3, 4, 6, 7}, 33: {11, 12, 14, 15, 17, 18, 22, 23, 25, 26, 28, 29}, 56: {34, 35, 37, 38, 40, 41, 45, 46, 48, 49, 51, 52}, 69: {65, 66, 59, 60, 62, 63}, 91: {81, 82, 84, 85, 87, 88}, 103: {96, 97, 99, 100, 93, 94}, 128: {118, 119, 121, 122, 124, 125}, 139: {129, 130, 132, 133, 135, 136}, 150: {144, 146, 147, 140, 141, 143}, 162: {152, 153, 155, 156, 158, 159}, 173: {163, 164, 166, 167, 169, 170}}, {58: {10, 33, 56}, 117: {69, 70, 71, 73, 74, 76, 77, 91, 103, 104, 105, 107, 108, 110, 111}, 176: {128, 139, 150, 162, 173}}, {178: {58, 117, 176}}]
    placement = place_lanes_piecewise(dependencies, 45)
    # placement = place_lanes_manually(dependencies[:3], 45)
    for thing in dependencies[1]:
        print(placement[thing])
    print(placement)
    print(len(dependencies[0]))
    print(max(placement[thing] for thing in dependencies[0]))
    

    # print(place_lanes_manually(dependencies, 45))

