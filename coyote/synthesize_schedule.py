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


class AlignmentSynthesizer:
    def __init__(self, program: List[Instr], warp_size: int, lanes: List[int], timeout=60, disallow_same_vec_same_dep=False):
        self.timeout = timeout

        self.num_instr = len(program)

        dep_graph = dependency_graph(program)

        adds, subs, mults = split_types(program)
        ops = ['+' if i in adds else ('-' if i in subs else '*') for i in range(self.num_instr)]

        self.opt = z3.Solver()
        self.opt.set('timeout', timeout * 1000)

        self._alignment = z3.IntVector('alignment', self.num_instr)
        self._lanes = z3.IntVector('lanes', self.num_instr)

        for i in range(self.num_instr):
            self.opt.add(self._alignment[i] >= 0)
            self.opt.add(self._lanes[i] >= 0)
            self.opt.add(self._lanes[i] < warp_size)

            for j in range(self.num_instr):
                self.opt.add(z3.Implies(self._alignment[i] == self._alignment[j], ops[i] == ops[j]))
                self.opt.add(z3.Implies(
                    z3.And(self._alignment[i] == self._alignment[j], self._lanes[i] == self._lanes[j]), i == j))
                
                if i != j and disallow_same_vec_same_dep and len(set(dep_graph[i]).intersection(set(dep_graph[j]))) > 0:
                    self.opt.add(self._alignment[i] != self._alignment[j])

            self.opt.add(self._lanes[i] == lanes[cast(int, program[i].dest.val)])
            for dep in dep_graph[i]:
                self.opt.add(self._alignment[i] > self._alignment[dep])
                self.opt.add(self._lanes[i] == self._lanes[dep])
                

    def add_bound(self, bound):
        for i in range(self.num_instr):
            self.opt.add(self._alignment[i] < bound)

    def solve(self) :
        result = self.opt.check()
        if result != z3.sat:
            return z3.unsat

        model = self.opt.model()
        schedule: list[int] = [model[s].as_long() for s in self._alignment] # type: ignore

        return schedule



def synthesize_alignment(program: List[Instr], warp: int, lanes: List[int]) -> List[int]:
    heights: Dict[int, int] = defaultdict(lambda: 0)
    for instr in program:
        left_height = heights[cast(int, instr.lhs.val)]
        right_height = heights[cast(int, instr.rhs.val)]
        heights[cast(int, instr.dest.val)] = max(left_height, right_height) + 1

    synthesizer = AlignmentSynthesizer(program, warp, lanes)
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