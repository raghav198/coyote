from __future__ import annotations
import abc
from typing import List, NoReturn, Set


def assert_exhaustive(_: NoReturn) -> NoReturn:
    assert False


class Expr:
    def __init__(self, *terms):
        self.terms = terms

    def sub(self, var, val):
        return Expr(*list(
            map(lambda t: val if t == var else t, self.terms)))

    def __repr__(self):
        return " + ".join(map(str, self.terms))


# nil case: ContChain()
class ContChain:
    def __init__(self):
        self.cont = None

    def letset(self, var, val):
        return self

    def compile(self):
        return self

    def __repr__(_):
        return ""


def concatenate(first: ContChain, second: ContChain):
    if first.cont.cont is None:
        first.cont = second
    else:
        first.cont = concatenate(first.cont, second)
    return first


class CopseIR:
    __metaclass__ = abc.ABCMeta


class Type1Phi(CopseIR):
    def __init__(self, lhs, rhs, true: CopseIR, false: CopseIR):
        self.lhs = lhs
        self.rhs = rhs
        self.true = true
        self.false = false

    def __repr__(self):
        return f"(phi1 \"{self.lhs}\" \"{self.rhs}\" {self.true} {self.false})"


class Type2Phi(CopseIR):
    def __init__(self, first: CopseIR, second: CopseIR, vars: List[str]):
        self.first = first
        self.second = second
        # self.vars = vars

        self.vars = vars

    def __repr__(self):
        return f"(phi2 ({self.vars}) {self.first} {self.second})"


class Compare(ContChain):
    def __init__(self, left: Expr, right: Expr,
                 true: ContChain, false: ContChain, cont: ContChain = ContChain(), type2=False):
        self.left = left
        self.right = right
        self.true = true
        self.false = false
        self.cont = cont
        self.type2 = type2

    def letset(self, var, val):
        return Compare(self.left.sub(var, val), self.right.sub(var, val), self.true.letset(var, val), self.false.letset(var, val), self.cont.letset(var, val))

    def compileType1(self):
        return Type1Phi(self.left, self.right,
                        concatenate(
                            self.true, self.cont).compile(),
                        concatenate(self.false, self.cont).compile())

    def compile(self):
        return self.compileType1()

    def __repr__(self):
        return f"if({self.left} < {self.right}) {{{self.true}}} else {{{self.false}}};{self.cont}"


class Assign(ContChain):
    def __init__(self, var: str, val: Expr, cont: ContChain = ContChain()):
        self.var = var
        self.val = val
        self.cont = cont

    def letset(self, var, val):
        return Assign(self.var, self.val.sub(var, val), self.cont.letset(var, val))

    def compile(self):
        return self.cont.letset(self.var, self.val).compile()

    def __repr__(self):
        return f"{self.var} = {self.val};{self.cont}"


class Output(ContChain, CopseIR):
    def __init__(self, args: List[Expr], secret=False):
        self.args = args
        self.secret = secret
        self.cont = None

    def letset(self, var, val):
        return Output([arg.sub(var, val) for arg in self.args], secret=self.secret)

    def compile(self):
        return self

    def __repr__(self):
        return f"({'secret-print' if self.secret else 'print'} {', '.join(map(str, self.args))})"


def compile(program: ContChain) -> CopseIR:
    def get_vars(program: ContChain) -> Set[str]:
        if isinstance(program, Compare):
            return get_vars(program.true) | get_vars(program.false) | get_vars(program.cont)
        elif isinstance(program, Assign):
            return {program.var} | get_vars(program.cont)
        elif isinstance(program, ContChain) or program is None:
            return set()
        print(type(program))
        assert_exhaustive(program)

    def compileTree(program: ContChain) -> CopseIR:
        if isinstance(program, Compare):
            if program.type2:
                raise TypeError(
                    'Type-2 phi node is only allowed in top-level conditionals!')
            true = compileTree(concatenate(
                program.true, program.cont))
            false = compileTree(concatenate(
                program.false, program.cont))
            return Type1Phi(program.left, program.right, true, false)
        elif isinstance(program, Assign):
            return compileTree(program.cont.letset(program.var, program.val))
        elif isinstance(program, Output):
            return program
        elif isinstance(program, ContChain):
            raise NotImplementedError
        assert_exhaustive(program)

    # find the first phi2 to split on
    cur = curTree = program
    while cur.cont is not None:
        if isinstance(cur, Compare) and cur.type2:
            nextStep = cur.cont
            cur.cont = None
            vars = list(get_vars(curTree))
            cur.cont = Output([Expr(v)
                               for v in vars], secret=True)
            cur.type2 = False

            return Type2Phi(compileTree(curTree), compile(nextStep), vars=vars)
        else:
            cur = cur.cont

    return compileTree(curTree)


"""
if (a < b + c) {
    x = 3;
} else {
    x = 5;
}
y = x + 2;
if (y < 6) {
    z = 1;
} else {
    z = 0;
}
"""

# change the "type2=True" to see the first conditional be treated as phi1 vs phi2
program = Compare(Expr("a"), Expr("b", "c"),
                  Assign("x", Expr(3)),
                  Assign("x", Expr(5)),

                  Assign("y", Expr("x", 2),
                         Compare(Expr("y"), Expr(6),
                                 Assign("z", Expr(1)),
                                 Assign("z", Expr(0)))), type2=True)


program = concatenate(program, Output([Expr("z")]))

"""
if (a < b + c) {
    if (a + c < 5) { // type1 conditional (cannot be made type2, try to change it and it throws an error)
        x = a + b;
    } else {
        x = b + c;
    }
    y = a + x;
} // type2 conditional
x = c;
z = x;
"""
program_nested = Compare(Expr("a"), Expr("b", "c"),
                         Compare(Expr("a", "c"), Expr(5),
                                 Assign(
                                     "x", Expr("a", "b")),
                                 Assign(
                                     "x", Expr("b", "c")),
                                 Assign("y", Expr("a", "x")), type2=False),
                         Assign("x", Expr("c"), Assign(
                             "y", Expr("b", "x"))),
                         Assign("z", Expr("x")), type2=True)

program_nested = concatenate(
    program_nested, Output([Expr("x"), Expr("y"), Expr("z")]))


def get_gcd(depth: int, phis=[]) -> ContChain:
    """Its not quite GCD but its close enough"""
    assert len(phis) in (0, depth)
    if depth == 0:
        return ContChain()
    return Compare(Expr(f"a{depth}"), Expr(f"b{depth}"),
                   Assign(f"b{depth-1}", Expr(f"a{depth}", f"b{depth}"),
                          Assign(f"a{depth-1}", Expr(f"a{depth}"))),
                   Assign(f"a{depth-1}", Expr(f"a{depth}", f"b{depth}"),
                          Assign(f"b{depth-1}", Expr(f"b{depth}"))),
                   get_gcd(depth - 1, phis[1:] if len(phis) else []), type2=(len(phis) and phis[0]))


# the 'phis' array specifies whether the comparison at each depth should be type 1 (0) or type 2 (1)
gcd_program = concatenate(
    get_gcd(6, phis=[0, 0, 1, 0, 0, 1]), Output([Expr("g")]))

if __name__ == '__main__':
    print(compile(program))
