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
        

def get_dependences(schedule: Schedule):
    producers: dict[int, set[int]] = defaultdict(set)
    consumers: dict[int, set[int]] = defaultdict(set)
    
    for i, inst in enumerate(schedule.instructions):
        if inst.lhs.reg:
            producers[i].add(cast(int, inst.lhs.val))
            producers[i].update(producers[cast(int, inst.lhs.val)])
        if inst.rhs.reg:
            producers[i].add(cast(int, inst.rhs.val))
            producers[i].update(producers[cast(int, inst.rhs.val)])
        
    for inst in producers:
        for prod in producers[inst]:
            consumers[prod].add(inst)
        
    return producers, consumers


def violations(schedule: Schedule, deps: dict[int, set[int]] | None = None):
    if deps == None:
        deps, _ = get_dependences(schedule)
        
    for instruction, dependences in deps.items():
        for dependence in dependences:
            if schedule.alignment[instruction] <= schedule.alignment[dependence]:
                yield (instruction, dependence)
        
        
def relax_blends(schedule: Schedule, rounds=1000, beta=0.05, t=10) -> Schedule:
    producers, consumers = get_dependences(schedule)
            
    def independent(ops: list[int]):
        return not any(i in producers[j] for i in ops for j in ops if i != j)
    
    current = count_blends(schedule, debug=False)
    # print(f'Starting with {current} blends...')
    
    for _ in range(rounds):
        
        if current == 0: # if at any point we have no blends
            break
        
        # update temperature
        t /= (1 + t * beta)
        
        # generate candidate solution
        candidate = cast(Schedule, deepcopy(schedule))
        step = randint(0, max(schedule.alignment)) # which step to look at
        # all the left/right operands of this vector insruction
        operations: list[int]
        if random() < 0.5:
            operations = [cast(int, schedule.instructions[o].lhs.val) for o in schedule.at_step(step) if schedule.instructions[o].lhs.reg]
        else:
            operations = [cast(int, schedule.instructions[o].rhs.val) for o in schedule.at_step(step) if schedule.instructions[o].rhs.reg]
        
        # if they don't depend on each other...
        if len(operations) and independent(operations):
            # print(f'Trying to group {operations}')
            # ...group by operation...
            grouped_ops: dict[str, list[int]] = defaultdict(list)
            for i in operations:
                grouped_ops[schedule.instructions[i].op].append(i)
            
            #...try to move each group to be computed in the same step
            for _, group in grouped_ops.items():
                new_step = choice([schedule.alignment[g] for g in group])
                for o in group:
                    incumbents = candidate.at_step(new_step).intersection(candidate.at_lane(candidate.lanes[o]))
                    # print(f'Trying to swap {o} with {incumbents}...')
                    # print(f'deps[{o}] = {producers[o]}, incumbent deps = { [producers[i] for i in incumbents] }')
                    
                    # make sure the incumbent doesn't move past any its dependences
                    if not all(all(candidate.alignment[o] > candidate.alignment[dep] for dep in producers[incumbent]) for incumbent in incumbents):
                        continue
                    if not all(all(candidate.alignment[o] < candidate.alignment[dep] for dep in consumers[incumbent]) for incumbent in incumbents):
                        continue
                    if not all(new_step > candidate.alignment[dep] for dep in producers[o]):
                        continue
                    if not all(new_step < candidate.alignment[dep] for dep in consumers[o]):
                        continue
                    # print('Swap ok, continuing...')
                    for incumbent in incumbents: # should be either 0 or 1
                        candidate.alignment[incumbent] = candidate.alignment[o]
                    candidate.alignment[o] = new_step
            
            any_violations = False
            for violation in violations(candidate, producers):
                print(f'[ERROR] Violation: {violation}')
                any_violations = True
            if any_violations:
                quit()
                    
            
        else:
            continue
                
        # compute the new cost of blending
        new_cost = count_blends(candidate)
        if new_cost < current or random() < exp((current - new_cost) / t):
            # decide whether or not to accept the new solution
            schedule = candidate
            current = new_cost
            
    # print(f'...relaxed to {count_blends(schedule, debug=True)} blends')
    return schedule
        
        