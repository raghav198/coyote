from __future__ import annotations
from typing import List, Literal, Tuple, Union
import z3
from time import time
from slp_playground import Expression, Plus, Times, CVar, fuzz_expr

WARP_SIZE = 20
FUZZ_SIZE = 10
FUZZ_PARAMS = 0, 0.6

T_op = Union[Literal['+'], Literal['*']]


class Atom:
    def __init__(self, n: Union[int, str]):
        self.n = n
        self.register = isinstance(n, int)

    def __repr__(self):
        if self.register:
            if self.n >= 0:
                return f'r{self.n}'
            return '#'
        return self.n


class TAC:
    def __init__(self, dest: int, left: Atom, right: Atom, op: T_op):
        self.dest = Atom(dest)
        self.left = left
        self.right = right
        self.op = op

    def __repr__(self):
        return f'{self.dest} = {self.left} {self.op} {self.right}'


class VecTAC:
    def __init__(self, dest: List[int], left: List[Atom], right: List[Atom], op: T_op):
        self.dest = [Atom(d) for d in dest]
        self.left = left
        self.right = right
        self.op = op

    def __repr__(self):
        return f'{self.dest} = {self.left} {self.op} {self.right}'


target = -1


def compile_to_3ac(e: Expression, acc: List[TAC]) -> Atom:
    global target
    if isinstance(e, CVar):
        return Atom(e.name)
    elif isinstance(e, Plus) or isinstance(e, Times):
        lhs = compile_to_3ac(e.lhs, acc)
        rhs = compile_to_3ac(e.rhs, acc)
        target += 1
        acc.append(TAC(target, lhs, rhs,
                       '+' if isinstance(e, Plus) else '*'))
        return Atom(target)

    raise NotImplementedError(
        f'Unknown subclass of Expression: {type(e)}')


def dependency_graph(program: List[TAC]) -> List[List[Atom]]:
    dependencies = []
    for line in program:
        line_deps = []
        if line.left.register:
            line_deps.append(line.left)
        if line.right.register:
            line_deps.append(line.right)
        dependencies.append(line_deps)

    return dependencies


def split_instruction_types(program: List[TAC]) -> Tuple[List[int], List[int]]:
    add_instrs = []
    mul_instrs = []
    for i, p in enumerate(program):
        if p.op == '+':
            add_instrs.append(i)
        else:
            mul_instrs.append(i)
    return add_instrs, mul_instrs


def build_vectorized_code(program: List[TAC], schedule: List[int], lanes: List[int], types: z3.ArrayRef) -> List[VecTAC]:
    vectorized_code = []
    # go from inst -> slot to slot -> [inst]
    inv_schedule = [[i for i in range(len(
        schedule)) if schedule[i] == slot] for slot in set(schedule)]

    # build the lanes for each slot
    for instrs in inv_schedule:
        dest = [-1 for _ in range(WARP_SIZE)]
        left = [Atom('#') for _ in range(WARP_SIZE)]
        right = [Atom('#') for _ in range(WARP_SIZE)]

        for i in instrs:
            dest[lanes[i]] = program[i].dest.n
            left[lanes[i]] = program[i].left
            right[lanes[i]] = program[i].right
        vectorized_code.append(
            VecTAC(dest, left, right, '+' if types[i] == itype.plus else '*'))

    return vectorized_code


# Fuzz some random expressions to test with
expr = []
if FUZZ_SIZE:
    for _ in range(FUZZ_SIZE):
        expr.append(fuzz_expr(*FUZZ_PARAMS))
else:
    e1 = Times(CVar('a'), Plus(CVar('b'), CVar('c')))
    e2 = Times(Plus(CVar('a'), CVar('b')),
               Plus(CVar('a'), CVar('b')))
    e3 = Plus(Times(CVar('a'), CVar('b')),
              Times(CVar('-2'), CVar('c')))

    expr = [e1, e2, e3]

# Compile to 3-address code to be vectorized
program: List[TAC] = []
print('Expressions: ')
for e in expr:
    print(e)
    compile_to_3ac(e, program)

print('Compiled 3-AC:')
print('\n'.join(map(str, program)))

dep_graph = dependency_graph(program)
adds, mults = split_instruction_types(program)
num_instr = len(program)

# Set up automatic vectorization using  Z3
# vars being solved for will start with '_' to distinguish from actual loaded values in model
opt = z3.Optimize()

itype = z3.Datatype('itype')  # instruction type (+/x)
itype.declare('plus')
itype.declare('times')
itype = itype.create()

# where in the vector schedule is each instruction placed?
_schedule = z3.IntVector('schedule', num_instr)
# which vector lane does each instruction output on?
_lanes = z3.IntVector('lanes', num_instr)
# which operation to do for each instruction (prevents mixing)
_types = z3.Array('types', z3.IntSort(), itype)
# how many total steps the program takes
_steps = z3.Int('steps')

# set up constraints
for i in range(num_instr):
    # set bounds
    opt.add(_schedule[i] >= 0)
    opt.add(_lanes[i] >= 0)
    opt.add(_schedule[i] <= num_instr)
    opt.add(_lanes[i] <= WARP_SIZE)
    # want to find total number of steps
    opt.add(_steps > _schedule[i])

    # enforce uniqueness
    for j in range(num_instr):
        opt.add(z3.Implies(z3.And(
            _schedule[i] == _schedule[j], _lanes[i] == _lanes[j]), i == j))

    # enforce output on the same lane as input
    for dep in dep_graph[i]:
        opt.add(_lanes[i] == _lanes[dep.n])

    if i in adds:
        opt.add(_types[_schedule[i]] == itype.plus)
    elif i in mults:
        opt.add(_types[_schedule[i]] == itype.times)


opt.minimize(_steps)
opt.set('timeout', 2 * 60 * 1000)  # 2 minutes
start = time()
res = opt.check()
end = time()
if res == z3.sat:
    print(f'Solved! Took {int(1000 * (end - start))} ms')
elif res == z3.unknown and opt.reason_unknown() == 'canceled':
    print(
        f'Cancelled after {int(1000 * (end - start))} ms (potentially due to timeout). Program may be suboptimal')

model = opt.model()
schedule = [model[s].as_long() for s in _schedule]
lanes = [model[l].as_long() for l in _lanes]
steps = model[_steps]

print('Vectorized code:')
print('\n'.join(map(str, build_vectorized_code(
    program, schedule, lanes, model[_types]))))

print(f'{steps} instructions compared to {len(program)}!')
print(f'Used {len(set(lanes))} lanes!')
