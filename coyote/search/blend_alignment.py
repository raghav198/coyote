from collections import defaultdict
from copy import deepcopy
from math import exp
from random import choice, randint, random
from typing import cast

from ..codegen import Schedule


def count_blends(schedule: Schedule, debug: bool = False) -> int:
    blends: int = 0
    for i in range(max(schedule.alignment) + 1):
        ops = schedule.at_step(i)
        left_srcs = {schedule.alignment[cast(int, schedule.instructions[o].lhs.val)] for o in ops if schedule.instructions[o].lhs.reg}
        right_srcs = {schedule.alignment[cast(int, schedule.instructions[o].rhs.val)] for o in ops if schedule.instructions[o].rhs.reg}
        if debug:
            print(i, left_srcs, right_srcs)
        blends += max(len(left_srcs) - 1, 0) + max(len(right_srcs) - 1, 0)
        
    return blends
        
def relax_blends(schedule: Schedule, rounds=1000, beta=0.05, t=10) -> Schedule:
    deps: dict[int, set[int]] = defaultdict(set)
    
    for i, inst in enumerate(schedule.instructions):
        if inst.lhs.reg:
            deps[i].add(cast(int, inst.lhs.val))
            deps[i].update(deps[cast(int, inst.lhs.val)])
        if inst.rhs.reg:
            deps[i].add(cast(int, inst.rhs.val))
            deps[i].update(deps[cast(int, inst.rhs.val)])
            
    def independent(ops: list[int]):
        return not any(i in deps[j] for i in ops for j in ops if i != j)
    
    current = count_blends(schedule, debug=False)
    print(f'Starting with {current} blends...')
    
    for _ in range(rounds):
        # update temperature
        t /= (1 + t * beta)
        
        # generate candidate solution
        candidate = cast(Schedule, deepcopy(schedule))
        step = randint(0, max(schedule.alignment)) # which step to look at
        # all the left/right operands of this vector insruction
        ops: list[int]
        if random() < 0.5:
            ops = [cast(int, schedule.instructions[o].lhs.val) for o in schedule.at_step(step) if schedule.instructions[o].lhs.reg]
        else:
            ops = [cast(int, schedule.instructions[o].rhs.val) for o in schedule.at_step(step) if schedule.instructions[o].rhs.reg]
        
        # if they don't depend on each other...
        if len(ops) and independent(ops):
            #...try to move them to all be computed in the same step
            new_step: int = choice([schedule.alignment[o] for o in ops])
            for o in ops:
                incumbents = candidate.at_step(new_step).intersection(candidate.at_lane(candidate.lanes[o]))
                for incumbent in incumbents: # should be either 0 or 1
                    candidate.alignment[incumbent] = candidate.alignment[o]
                candidate.alignment[o] = new_step
        else:
            continue
                
        # compute the new cost of blending
        new_cost = count_blends(candidate)
        if random() < exp((current - new_cost) / t):
            # decide whether or not to accept the new solution
            schedule = candidate
            current = new_cost
            
    print(f'...relaxed to {count_blends(schedule, debug=False)} blends')
    return schedule
        
        