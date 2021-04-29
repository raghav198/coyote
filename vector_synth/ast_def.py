from typing import Dict, List, Union, Any
from random import choice, random, seed
from string import ascii_lowercase

Expression = Union['Var', 'Op']

#T_op = Union[Literal['+'], Literal['*']]
T_op = Any
BLANK_SYMBOL = '_'


class Var:
    def __init__(self, name: str):
        self.name = name
        self.tag = name
        self.subtags = []

    def __str__(self) -> str:
        return self.name

    def __repr__(self) -> str:
        return f'Var("{self.name}")'

    def __eq__(self, o: object) -> bool:
        return isinstance(o, Var) and o.name == self.name


class Op:
    def __init__(self, op: str, lhs: Expression, rhs: Expression):
        self.op = op
        self.lhs = lhs
        self.rhs = rhs
        self.tag: int = -1
        self.subtags: List[int] = []

    def __str__(self) -> str:
        return f'({str(self.lhs)} {self.op} {str(self.rhs)})'

    def __repr__(self) -> str:
        return f'Op("{self.op}", {repr(self.lhs)}, {repr(self.rhs)})'

    def __eq__(self, o: object) -> bool:
        return isinstance(o, Op) and o.op == self.op and o.lhs == self.lhs and o.rhs == self.rhs


def plus(a, b):
    return Op('+', a, b)


def times(a, b):
    return Op('*', a, b)


class Atom:
    def __init__(self, x: Union[int, str]):
        self.val = x
        self.reg = isinstance(x, int)

    def __repr__(self) -> str:
        if self.reg and self.val >= 0:
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
    def __init__(self, tag_lookup: Dict[int, Op]):
        self.code: List[Instr] = []
        self.target = -1
        self.tag_lookup = tag_lookup
        self.code_lookup: Dict[int, List[Instr]] = {}

    def compile(self, e: Expression) -> Atom:
        if isinstance(e, Var):
            return Atom(e.name)

        assert isinstance(e, Op)

        lhs = self.compile(e.lhs)
        rhs = self.compile(e.rhs)

        self.target += 1
        e.tag = self.target
        e.subtags = e.lhs.subtags + e.rhs.subtags + [e.lhs.tag, e.rhs.tag]
        self.tag_lookup[e.tag] = e

        self.code.append(Instr(self.target, lhs, rhs, e.op))

        self.code_lookup[e.tag] = []
        if e.lhs.tag in self.code_lookup:
            self.code_lookup[e.tag].extend(
                self.code_lookup[e.lhs.tag])
        if e.rhs.tag in self.code_lookup:
            self.code_lookup[e.tag].extend(
                self.code_lookup[e.rhs.tag])
        self.code_lookup[e.tag].append(self.code[-1])

        return Atom(self.target)


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