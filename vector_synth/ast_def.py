from collections import defaultdict
from typing import Dict, List, Optional, Set, Union, Any
from random import choice, random, seed
from string import ascii_lowercase

Expression = Union['Var', 'Op']

# T_op = Union[Literal['+'], Literal['*']]
T_op = Any
BLANK_SYMBOL = '_'


class Var:
    def __init__(self, name: str):
        self.name = name
        self.tag = None#name
        self.subtags: List[Union[int, str]] = []

    def __add__(self, other):
        return Op('+', self, other)

    def __mul__(self, other):
        return Op('*', self, other)

    def __sub__(self, other):
        return Op('-', self, other)

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return f'Var("{self.name}")'

    def __eq__(self, o: object) -> bool:
        return isinstance(o, Var) and o.name == self.name

    def __hash__(self) -> int:
        return hash(self.name)


class Op:
    def __init__(self, op: str, lhs: Expression, rhs: Expression):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs
        self.tag: Optional[int] = None
        self.subtags: List[Union[int, str]] = []

    def __add__(self, other):
        return Op('+', self, other)

    def __mul__(self, other):
        return Op('*', self, other)

    def __sub__(self, other):
        return Op('-', self, other)

    def __str__(self) -> str:
        return f'({str(self.lhs)} {self.op} {str(self.rhs)})'

    def __repr__(self) -> str:
        return f'Op("{self.op}", {repr(self.lhs)}, {repr(self.rhs)})'

    def __eq__(self, o: object) -> bool:
        return isinstance(o, Op) and o.op == self.op and o.lhs == self.lhs and o.rhs == self.rhs

class Tree:
    def __init__(self, a):
        if type(a) is str:
            a = Var(a)
        self.a = a
    
    def __add__(self, o):
        if self.a == 0:
            return Tree(o.a)
        if o.a == 0:
            return Tree(self.a)
        return Tree(Op('+', self.a, o.a))
    
    def __mul__(self, o):
        if (self.a == 0 or o.a == 0):
            return Tree(0)
        return Tree(Op('*', self.a, o.a))
    
    def __sub__(self, o):
        return Tree(Op('-', self.a, o.a))

def plus(a, b):
    if type(a) is str:
        a = Var(a)
    if type(b) is str:
        b = Var(b)

    return Op('+', a, b)

def minus(a, b):
    if type(a) is str:
        a = Var(a)
    if type(b) is str:
        b = Var(b)

    return Op('-', a, b)

def times(a, b):
    if type(a) is str:
        a = Var(a)
    if type(b) is str:
        b = Var(b)

    return Op('*', a, b)


def minus(a, b):
    if type(a) is str:
        a = Var(a)
    if type(b) is str:
        b = Var(b)
    
    return Op('-', a, b)


def is_reg(atom):
    return isinstance(atom.val, int)


class Atom:
    def __init__(self, x: Union[int, str]):
        self.val = x
        self.reg = isinstance(x, int)

    def __repr__(self) -> str:
        if isinstance(self.val, int) and self.val >= 0:
            return f'%{self.val}'
        elif self.reg:
            return BLANK_SYMBOL

        return str(self.val)

    def __eq__(self, other) -> bool:
        """This function is dedicated to Vani, in loving memory RIP"""
        return self.reg == other.reg and self.val == other.val


class Instr:
    def __init__(self, dest: int, lhs: Atom, rhs: Atom, op: str):
        self.dest = Atom(dest)
        self.lhs = lhs
        self.rhs = rhs
        self.op = op

    def __repr__(self) -> str:
        return f'Instr({self.dest}, {self.lhs}, {self.rhs}, {self.op})'

    def __str__(self) -> str:
        return f'{str(self.dest)} = {str(self.lhs)} {self.op} {str(self.rhs)}'


class Compiler:
    def __init__(self, tag_lookup: Dict[int, Expression], input_groups: List[Set[str]] = [], allow_replicating=[]):
        self.code: List[Instr] = []
        self.exprs: List[Expression] = []
        self.target = -1
        self.tag_lookup = tag_lookup
        self.code_lookup: Dict[int, List[Instr]] = {}

        self.loaded_regs: Dict[str, int] = {}
        self.input_groups = input_groups
        self.allow_duplicates: Set[str] = set()
        if allow_replicating == 'all':
            self.replicate_all = True
        else:
            self.replicate_all = False
            for thing in allow_replicating:
                if isinstance(thing, int):
                    self.allow_duplicates |= self.input_groups[thing]
                else:
                    self.allow_duplicates.add(thing)

    def compile(self, e: Expression, top=True) -> Atom:
        if isinstance(e, Var):

            if all(e.name not in group for group in self.input_groups):
                return Atom(e.name)

            # return Atom(e.name)

            # if not self.allow_duplicates and (e.name in self.loaded_regs):
            if not self.replicate_all and e.name not in self.allow_duplicates and e.name in self.loaded_regs:
                print(f'Reusing {self.loaded_regs[e.name]} instead of reloading {e.name}')
                e.tag = self.loaded_regs[e.name]
                return Atom(self.loaded_regs[e.name])

            self.target += 1
            e.tag = self.target
            self.code.append(Instr(self.target, Atom(e.name), Atom(e.name), '~'))
            self.tag_lookup[self.target] = e

            self.loaded_regs[e.name] = self.target

            return Atom(self.target)

        assert isinstance(e, Op)

        if top:
            self.exprs.append(e)
        lhs = self.compile(e.lhs, top=False)
        rhs = self.compile(e.rhs, top=False)

        self.target += 1
        e.tag = self.target
        e.subtags = e.lhs.subtags + e.rhs.subtags + [e.lhs.tag, e.rhs.tag]
        self.tag_lookup[e.tag] = e

        self.code.append(Instr(self.target, lhs, rhs, e.op))

        self.code_lookup[e.tag] = []
        if e.lhs.tag in self.code_lookup:
            assert isinstance(e.lhs.tag, int)  # mypy
            self.code_lookup[e.tag].extend(
                self.code_lookup[e.lhs.tag])
        if e.rhs.tag in self.code_lookup:
            assert isinstance(e.rhs.tag, int)  # mypy
            self.code_lookup[e.tag].extend(
                self.code_lookup[e.rhs.tag])
        self.code_lookup[e.tag].append(self.code[-1])

        return Atom(self.target)


class CompilerV2:
    def __init__(self, input_groups: List[Set[str]] = [], allow_replicating=[]):
        self.code: List[Instr] = []
        self.tag_lookup: Dict[int, Expression] = {}
        self.dependences: Dict[int, Set[int]] = defaultdict(set)
        self.next_temp = -1

        self.loaded_regs: Dict[str, int] = {}
        self.input_groups = input_groups
        self.allow_duplicates: Set[str] = set()
        if allow_replicating == 'all':
            self.replicate_all = True
        else:
            self.replicate_all = False
            for thing in allow_replicating:
                if isinstance(thing, int):
                    self.allow_duplicates |= self.input_groups[thing]
                else:
                    self.allow_duplicates.add(thing)

    def compile(self, e: Expression):
        if isinstance(e, Var):
            # is this variable not supposed to be grouped?
            if all(e.name not in group for group in self.input_groups):
                # directly use it without emitting a load
                return Atom(e.name)
            
            # this variable shouldn't be replicated, and its already loaded into a register
            if not self.replicate_all and e.name not in self.allow_duplicates and e.name in self.loaded_regs:
                # there is already a register that loads it
                e.tag = self.loaded_regs[e.name]
                return Atom(self.loaded_regs[e.name])

            # otherwise, emit a load instruction
            self.next_temp += 1
            e.tag = self.next_temp
            self.code.append(Instr(self.next_temp, Atom(e.name), Atom(e.name), '~'))
            self.tag_lookup[self.next_temp] = e
            self.loaded_regs[e.name] = self.next_temp

            return Atom(self.next_temp)

        assert isinstance(e, Op)
        if e.lhs.tag is None:
            self.compile(e.lhs)
        if e.rhs.tag is None:
            self.compile(e.rhs)
        # if e.lhs.tag is None:
        #     lhs = self.compile(e.lhs)
        # else:
        #     lhs = self.tag_lookup[e.lhs.tag]

        # if e.rhs.tag is None:
        #     rhs = self.compile(e.rhs)
        # else:
        #     rhs = self.tag_lookup[e.rhs.tag]

        self.next_temp += 1
        e.tag = self.next_temp
        self.dependences[e.tag] = self.dependences[e.lhs.tag] | self.dependences[e.rhs.tag] | {e.lhs.tag, e.rhs.tag}
        self.tag_lookup[e.tag] = e

        self.code.append(Instr(self.next_temp, Atom(e.lhs.tag), Atom(e.rhs.tag), e.op))
        return Atom(self.next_temp)



def fuzzer(step, term=0) -> Expression:
    sel = random()
    nterm = 1 - (1 - term) * step
    if sel < term:
        return Var(choice(ascii_lowercase))
    else:
        lhs = fuzzer(step, nterm)
        rhs = fuzzer(step, nterm)
        if sel < (term + 1) / 2:
            return plus(lhs, rhs)
        else:
            return times(lhs, rhs)


if __name__ == '__main__':
    e = fuzzer(0.5)
    print(e)
    c = Compiler({})
    c.compile(e)
    print('\n'.join(map(str, c.code)))

    print(e.tag)
