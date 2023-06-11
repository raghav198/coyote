        
from collections import defaultdict
from copy import copy
from math import exp
from random import choice, randint, random
from typing import cast
from .coyote_ast import Instr


def count_blends(sched: list[int], instr: list[Instr]) -> int:
    def instrs_at(step: int) -> set[int]:
        return {i for i in sched if sched[i] == step}
    
    blends: int = 0
    for i in range(max(sched) + 1):
        ops = instrs_at(i)
        blends += len({sched[cast(int, instr[o].lhs.val)] for o in ops if instr[o].lhs.reg})
        blends += len({sched[cast(int, instr[o].rhs.val)] for o in ops if instr[o].lhs.reg})
        
    return blends
        
def relax_blends(sched: list[int], instr: list[Instr], rounds=1000, beta=0.05, t=10) -> list[int]:
    def instrs_at(step: int) -> set[int]:
        return {i for i, s in enumerate(sched) if s == step}
    
    deps: dict[int, set[int]] = defaultdict(set)
    
    for i, inst in enumerate(instr):
        if inst.lhs.reg:
            deps[i].add(cast(int, inst.lhs.val))
            deps[i].update(deps[cast(int, inst.lhs.val)])
        if inst.rhs.reg:
            deps[i].add(cast(int, inst.rhs.val))
            deps[i].update(deps[cast(int, inst.rhs.val)])
            
    def independent(ops: list[int]):
        return not any(i in deps[j] for i in ops for j in ops if i != j)
    
    current = count_blends(sched, instr)
    print(f'Starting with {current} blends...')
    
    for _ in range(rounds):
        # update temperature
        t /= (1 + t * beta)
        
        # generate candidate solution
        candidate = copy(sched)
        step = randint(0, max(sched)) # which step to look at
        # all the left/right operands of this vector insruction
        # print(step, instrs_at(step))
        ops: list[int] = [cast(int, instr[o].lhs.val) for o in instrs_at(step) if instr[o].lhs.reg] if random() < 0.5 else [cast(int, instr[o].rhs.val) for o in instrs_at(step) if instr[o].rhs.reg]
        
        # if they don't depend on each other...
        if len(ops) and independent(ops):
            #...try to move them to all be computed in the same step
            dest: int = choice([sched[o] for o in ops])
            for o in ops:
                candidate[o] = dest
        else:
            continue
                
        # compute the new cost of blending
        new_cost = count_blends(candidate, instr)
        if random() < exp((current - new_cost) / t):
            # decide whether or not to accept the new solution
            sched = candidate
            current = new_cost
            
       
    return sched
        
        