from random import random, choice
from typing import List, Tuple


class Expression:

    nextvar = -1

    @classmethod
    def getnext(cls):
        Expression.nextvar += 1
        return Expression.nextvar

    def compile(_) -> Tuple[List[str], str]:
        raise NotImplemented


class CVar(Expression):
    def __init__(self, name: str):
        self.name = name

    def compile(self) -> Tuple[List[str], str]:
        return [], self.name

    def __repr__(self) -> str:
        return self.name


class Plus(Expression):
    def __init__(self, a: Expression, b: Expression):
        self.lhs = a
        self.rhs = b

    def compile(self) -> Tuple[List[str], str]:
        lhs, l = self.lhs.compile()
        rhs, r = self.rhs.compile()
        code = lhs + rhs
        temp = f'r{Expression.getnext()}'

        return code + [f'{temp} = {l} + {r}'], temp

    def __repr__(self) -> str:
        return f'({self.lhs} + {self.rhs})'


class Times(Expression):
    def __init__(self, a: Expression, b: Expression):
        self.lhs = a
        self.rhs = b

    def compile(self) -> Tuple[List[str], str]:
        lhs, l = self.lhs.compile()
        rhs, r = self.rhs.compile()
        code = lhs + rhs
        temp = f't{Expression.getnext()}'
        return code + [f'{temp} = {l} * {r}'], temp

    def __repr__(self) -> str:
        return f'({self.lhs} * {self.rhs})'


var = 0
alphabet = 'abcdefghijklm'


def fuzz_expr(term=0.4, step=0.6) -> Expression:
    global var
    which = random()
    updated_term = 1 - (1 - term) * step
    if which < term:
        var += 1
        return CVar(choice(alphabet))
    elif which < (term + 1) / 2:
        lhs = fuzz_expr(updated_term)
        rhs = fuzz_expr(updated_term)
        return Plus(lhs, rhs)
    else:
        lhs = fuzz_expr(updated_term)
        rhs = fuzz_expr(updated_term)
        return Times(lhs, rhs)


# e1 = fuzz_expr(term=0.1)
# e2 = fuzz_expr(term=0.1)

# print('First:')
# print(e1)
# print('\n'.join(e1.compile()[0]))
# print(e2)
# print('\n'.join(e2.compile()[0]))

if __name__ == '__main__':
    e1 = Times(CVar('x'), Plus(CVar('y'), CVar('z')))
    e2 = Times(Plus(CVar('x'), CVar('y')),
               Plus(CVar('x'), CVar('y')))
    e3 = Plus(Times(CVar('x'), CVar('y')),
              Times(CVar('-2'), CVar('z')))

    print(e1)
    print(e2)
    print(e3)
    print('\n'.join(e1.compile()[0]))
    print('\n'.join(e2.compile()[0]))
    print('\n'.join(e3.compile()[0]))
