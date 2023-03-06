from collections import defaultdict
from dataclasses import dataclass
from typing import Tuple, cast

from .coyote_ast import *
import z3 # type: ignore
from sys import stderr
from time import time

# z3.set_option('parallel.enable', True)


class VecSchedule:
    def __init__(self, dest: List[int] | List[Atom], left: List[Atom], right: List[Atom], op: T_op):
        self.dest = [Atom(d) if isinstance(d, int) else d for d in dest]
        self.left = left
        self.right = right
        self.op = op

    def __repr__(self):
        return f'{self.dest} = {self.left} {self.op} {self.right}'

    def copy(self):
        return VecSchedule(self.dest[:], self.left[:], self.right[:], self.op)


def dependency_graph(program: List[Instr]) -> List[List[int]]:
    def lookup(reg: int) -> List[int]:
        # return next((i for i in range(len(program)) if program[i].dest.val == reg), -1)
        return list((i for i in range(len(program)) if program[i].dest.val == reg))
    graph: List[List[int]] = []
    for line in program:
        deps = []
        if line.lhs.reg:
            assert isinstance(line.lhs.val, int)
            deps.extend(lookup(line.lhs.val))
        #     deps.append(lookup(line.lhs.val))
        # else:
        #     deps.append(-1)
        if line.rhs.reg:
            assert isinstance(line.rhs.val, int)
            deps.extend(lookup(line.rhs.val))
        #     deps.append(lookup(line.rhs.val))
        # else:
        #     deps.append(-1)
        graph.append(deps)

    return graph


def split_types(program: List[Instr]) -> Tuple[List[int], List[int], List[int]]:
    add_instrs = []
    mul_instrs = []
    sub_instrs = []

    for i, line in enumerate(program):
        if line.op == '+':
            add_instrs.append(i)
        elif line.op == '-':
            sub_instrs.append(i)
        elif line.op == '*':
            mul_instrs.append(i)
        elif line.op == '~':
            pass # loads get packed together anyway
        else:
            raise Exception(f'Unrecognized operand in instruction {line}: {line.op}')

    return add_instrs, sub_instrs, mul_instrs


class ScheduleSynthesizer:
    def __init__(self, program: List[Instr], warp_size: int, lanes: List[int], log=stderr, timeout=60, disallow_same_vec_same_dep=False):
        self.timeout = timeout
        self.log = log

        self.num_instr = len(program)

        dep_graph = dependency_graph(program)

        adds, subs, mults = split_types(program)
        ops = ['+' if i in adds else ('-' if i in subs else '*') for i in range(self.num_instr)]

        self.opt = z3.Solver()
        self.opt.set('timeout', timeout * 1000)

        self._schedule = z3.IntVector('schedule', self.num_instr)
        self._lanes = z3.IntVector('lanes', self.num_instr)

        for i in range(self.num_instr):
            self.opt.add(self._schedule[i] >= 0)
            self.opt.add(self._lanes[i] >= 0)
            self.opt.add(self._lanes[i] < warp_size)

            for j in range(self.num_instr):
                self.opt.add(z3.Implies(self._schedule[i] == self._schedule[j], ops[i] == ops[j]))
                self.opt.add(z3.Implies(
                    z3.And(self._schedule[i] == self._schedule[j], self._lanes[i] == self._lanes[j]), i == j))
                
                if i != j and disallow_same_vec_same_dep and len(set(dep_graph[i]).intersection(set(dep_graph[j]))) > 0:
                    # instructions i and j share a dependency
                    # print(f'Disallowing {i} and {j}')
                    self.opt.add(self._schedule[i] != self._schedule[j])

            self.opt.add(self._lanes[i] == lanes[cast(int, program[i].dest.val)])
            for dep in dep_graph[i]:
                self.opt.add(self._schedule[i] > self._schedule[dep])
                self.opt.add(self._lanes[i] == self._lanes[dep])
                

    def add_bound(self, bound):
        # print(f'Bounding by {bound}')
        for i in range(self.num_instr):
            self.opt.add(self._schedule[i] < bound)

    def solve(self) :
        result = self.opt.check()
        if result != z3.sat:
            return z3.unsat

        model = self.opt.model()
        schedule: list[int] = [model[s].as_long() for s in self._schedule] # type: ignore

        # print(f'Current solution: {schedule}')

        return schedule


def synthesize_schedule_bounded_consider_blends(program: List[Instr], max_len: int, log=stderr):
    timeout = 60
    num_instr = len(program)

    dep_graph = dependency_graph(program)

    adds, subs, mults = split_types(program)
    ops = ['+' if i in adds else ('-' if i in subs else '*') for i in range(num_instr)]

    opt = z3.Solver()
    opt.set('timeout', timeout * 1000)

    _schedule = z3.IntVector('schedule', num_instr)

    blend_penalty = z3.Sum([z3.If(z3.And(_schedule[i] == _schedule[j],
                                         z3.Or(_schedule[dep_graph[i][0]] != _schedule[dep_graph[j][0]],
                                               _schedule[dep_graph[i][1]] != _schedule[dep_graph[j][1]])), 1, 0)
                            for i in range(num_instr) for j in range(num_instr)])

    for i in range(num_instr):
        opt.add(_schedule[i] >= 0)
        if max_len >= 0:
            opt.add(_schedule[i] + blend_penalty < max_len)

        for j in range(num_instr):
            opt.add(z3.Implies(_schedule[i] == _schedule[j], ops[i] == ops[j]))

        for dep in dep_graph[i]:
            if dep == -1:
                continue
            opt.add(_schedule[i] > _schedule[dep])

    # print(f'Trying to synthesize {max_len} instructions...', file=log, end='')
    log.flush()
    start = time()
    res = opt.check()
    end = time()
    # print(f'({int(1000 * (end - start))} ms)', file=log)
    if res != z3.sat:
        return z3.unsat

    model = opt.model()

    schedule = [model[s].as_long() for s in _schedule] # type: ignore

    return schedule, model.eval(blend_penalty).as_long() # type: ignore


def synthesize_schedule_bounded(program: List[Instr], warp: int, max_len: int, log=stderr):
    dep_graph = dependency_graph(program)
    adds, subs, mults = split_types(program)

    num_instr = len(program)

    opt = z3.Solver()

    itype = z3.Datatype('itype')
    itype.declare('plus')
    itype.declare('minus')
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
            if dep == -1:
                continue
            opt.add(_lanes[i] == _lanes[dep])
            opt.add(_schedule[i] > _schedule[dep])

        if i in adds:
            opt.add(_types[_schedule[i]] == itype.plus)
        elif i in subs:
            opt.add(_types[_schedule[i]] == itype.minus)
        elif i in mults:
            opt.add(_types[_schedule[i]] == itype.times)

    # print(f'Trying to synthesize {max_len} instructions...', file=log, end='')
    log.flush()
    start = time()
    res = opt.check()
    end = time()
    print(f'({int(1000 * (end - start))} ms)', file=log)
    if res == z3.unsat:
        return res

    model = opt.model()

    schedule = [model[s].as_long() for s in _schedule] # type: ignore
    # lanes = [model[lane].as_long() for lane in _lanes]
    # types: List[T_op] = [('+' if model[_types][t] == itype.plus else '*') for t in range(num_instr)]

    return schedule


def synthesize_schedule_iterative_refine(program: List[Instr], timeout=10, log=stderr) -> List[int]:
    num_instr = len(program)
    dep_graph = dependency_graph(program)

    adds, subs, muls = split_types(program)
    ops = ['+' if i in adds else ('-' if i in subs else '*') for i in range(num_instr)]

    # build the model
    opt = z3.Solver()
    opt.set('timeout', timeout * 1000)

    _schedule = z3.IntVector('schedule', num_instr)
    blend_penalty = z3.Sum([z3.If(z3.And(_schedule[i] == _schedule[j],
                                         z3.Or(_schedule[dep_graph[i][0]] != _schedule[dep_graph[j][0]],
                                               _schedule[dep_graph[i][1]] != _schedule[dep_graph[j][1]])), 1, 0)
                            for i in range(num_instr) for j in range(num_instr)])

    for i in range(num_instr):
        opt.add(_schedule[i] >= 0)

        for j in range(num_instr):
            opt.add(z3.Implies(_schedule[i] == _schedule[j], ops[i] == ops[j]))

        for dep in dep_graph[i]:
            if dep == -1:
                continue
            opt.add(_schedule[i] > _schedule[dep])

    opt.push()
    print('Synthesizing a program', file=log)

    while True:
        schedule = []
        result = opt.check()
        if result == z3.sat:
            model = opt.model()
            schedule = [model[s].as_long() for s in _schedule] # type: ignore
            # print(type(schedule), schedule)
            # print(type(blend_penalty), blend_penalty)
            total_cost = max(schedule) + cast(int, model.eval(blend_penalty))
            print(total_cost, type(total_cost))
            print(f'Current cost: {total_cost}, attempting to refine...', file=log)

            for i in range(num_instr):
                opt.add(_schedule[i] + blend_penalty < total_cost)
        else:
            opt.pop()
            print('Cannot refine further')
            return schedule



def synthesize_schedule(program: List[Instr], warp: int, lanes: List[int], log=stderr) -> List[int]:
    # print(f'Calculating height...', file=log, end='')
    log.flush()
    heights: Dict[int, int] = defaultdict(lambda: 0)
    for instr in program:
        left_height = heights[cast(int, instr.lhs.val)]
        right_height = heights[cast(int, instr.rhs.val)]
        heights[cast(int, instr.dest.val)] = max(left_height, right_height) + 1

    max_height = max(heights.values())
    # print(f'({max_height})', file=log)
    start = time()

    synthesizer = ScheduleSynthesizer(program, warp, lanes, log=log)
    # synthesizer.add_bound(4 * max_height)
    synthesizer.add_bound(len(program))
    best_so_far = None
    while True:
        answer = synthesizer.solve()
        if answer == z3.unsat:
            if best_so_far is None:
                raise Exception("No model was ever found!")
            return best_so_far
        assert isinstance(answer, list)
        best_so_far = answer
        synthesizer.add_bound(max(answer))