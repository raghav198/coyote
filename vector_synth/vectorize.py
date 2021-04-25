from typing import Tuple

from ast_def import *
import z3
from sys import stderr
from time import time


class VecInstr:
    def __init__(self, dest: List[int], left: List[Atom], right: List[Atom], op: T_op):
        self.dest = [Atom(d) for d in dest]
        self.left = left
        self.right = right
        self.op = op

    def __repr__(self):
        return f'{self.dest} = {self.left} {self.op} {self.right}'


def dependency_graph(program: List[Instr]) -> List[List[int]]:
    def lookup(reg: int) -> List[int]:
        return list(i for i in range(len(program)) if program[i].dest.val == reg)

    graph: List[List[int]] = []
    for line in program:
        deps = []
        if line.lhs.reg:
            deps.extend(lookup(line.lhs.val))
        if line.rhs.reg:
            deps.extend(lookup(line.rhs.val))
        graph.append(deps)

    return graph


def split_types(program: List[Instr]) -> Tuple[List[int], List[int]]:
    add_instrs = []
    mul_instrs = []

    for i, line in enumerate(program):
        if line.op == '+':
            add_instrs.append(i)
        else:
            mul_instrs.append(i)

    return add_instrs, mul_instrs


def synthesize_schedule_bounded(program: List[Instr], warp: int, max_len: int):
    dep_graph = dependency_graph(program)
    adds, mults = split_types(program)

    num_instr = len(program)

    opt = z3.Solver()

    itype = z3.Datatype('itype')
    itype.declare('plus')
    itype.declare('times')
    itype = itype.create()

    # when does the instruction get evaluated
    _schedule = z3.IntVector('schedule', num_instr)
    # which thread executes the instruction
    _lanes = z3.IntVector('lanes', num_instr)
    # prevent mixing adds and multiplies
    _types = z3.Array('types', z3.IntSort(), itype)

    # set up constraints
    for i in range(num_instr):
        # bounds
        opt.add(_schedule[i] >= 0)
        opt.add(_lanes[i] >= 0)
        opt.add(_schedule[i] < max_len)
        opt.add(_lanes[i] < warp)

        # uniqueness
        for j in range(num_instr):
            opt.add(z3.Implies(z3.And(
                _schedule[i] == _schedule[j], _lanes[i] == _lanes[j]), i == j))

        # no shuffling
        for dep in dep_graph[i]:
            opt.add(_lanes[i] == _lanes[dep])
            opt.add(_schedule[i] > _schedule[dep])

        if i in adds:
            opt.add(_types[_schedule[i]] == itype.plus)
        elif i in mults:
            opt.add(_types[_schedule[i]] == itype.times)

    start = time()
    res = opt.check()
    end = time()
    if res == z3.unsat:
        return res

    print(f'Synthesized schedule in {int(1000 * (end - start))}ms', file=stderr)
    model = opt.model()

    schedule = [model[s].as_long() for s in _schedule]
    lanes = [model[lane].as_long() for lane in _lanes]
    types: List[T_op] = [('+' if model[_types][t] == itype.plus else '*') for t in range(num_instr)]

    return schedule, lanes, types


def synthesize_schedule(program: List[Instr], warp: int) -> List[int]:
    for max_len in range(len(program) + 1):
        result = synthesize_schedule_bounded(program, warp, max_len)
        if result == z3.unsat:
            continue

        schedule, *_ = result
        return schedule


def build_vector_program_automatic(program: List[Instr], warp: int) -> List[VecInstr]:

    def __sweep_length():
        for max_len in range(len(program) + 1):
            print(f'Trying length {max_len} program...', file=stderr)
            result = synthesize_schedule_bounded(program, warp, max_len)
            if result == z3.unsat:
                continue
            print('Successful!', file=stderr)
            return result

    vectorized_code = []

    schedule, lanes, types = __sweep_length()

    # schedule  :: inst -> slot, inv_schedule :: slot -> [inst]
    inv_schedule = [[i for i in range(len(schedule)) if schedule[i] == slot]
                    for slot in set(schedule)]

    for instrs in inv_schedule:
        dest = [-1 for _ in range(warp)]
        lhs = [Atom(BLANK_SYMBOL) for _ in range(warp)]
        rhs = [Atom(BLANK_SYMBOL) for _ in range(warp)]

        for i in instrs:
            dest[lanes[i]] = program[i].dest.val
            lhs[lanes[i]] = program[i].lhs
            rhs[lanes[i]] = program[i].rhs

        vectorized_code.append(VecInstr(dest, lhs, rhs, types[i]))

    return vectorized_code


def build_vector_program(program: List[Instr], lanes: List[int], schedule: List[int]):
    print('Building stage:')
    print('\n'.join(map(str, program)))
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
            print(f'Instruction {i} goes on lane {lane_num}!')
            dest[lane_num] = program[i].dest.val
            lhs[lane_num] = program[i].lhs
            rhs[lane_num] = program[i].rhs

        vectorized_code.append(VecInstr(dest, lhs, rhs, program[i].op))

    return vectorized_code
