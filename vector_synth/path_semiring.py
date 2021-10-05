from itertools import product
from typing import Generic, Iterable, List, Protocol, Set, Tuple, TypeVar, Type
from graph import Node, Graph, Edge


S = TypeVar('S', bound='Semiring')
class Semiring(Protocol):
    def __add__(self: S, other: S) -> S:
        ...

    def __mul__(self: S, other: S) -> S:
        ...

    @staticmethod
    def zero() -> S:
        ...

    @staticmethod
    def one() -> S:
        ...

# T = TypeVar('T', covariant=True, bound=Semiring)
# Matrix = List[List[T]]

Mat = TypeVar('Mat', bound='Semiring')
class Matrix(Generic[Mat]):
    def __init__(self, mat: Type[Mat], n: int):
        self.mat = mat
        self.vals: List[List[Mat]] = [[mat.zero() for _ in range(n)] for _ in range(n)]
        self.n = n

    def __add__(self, other: 'Matrix[Mat]') -> 'Matrix[Mat]':
        new = Matrix(self.mat, self.n)
        for i in range(self.n):
            for j in range(self.n):
                new.vals[i][j] = self.vals[i][j] + other.vals[i][j]

        return new

    def __mul__(self, other: 'Matrix[Mat]') -> 'Matrix[Mat]':
        new = Matrix(self.mat, self.n)
        for i in range(self.n):
            for j in range(i + 1):
                new.vals[i][j] = sum([self.vals[i][k] * other.vals[k][j] for k in range(self.n)], self.mat.zero())
                # print(new.vals[i][j].vals)
                
                new.vals[j][i] = new.vals[i][j]
        # input()
        return new

    def __eq__(self, other) -> bool:
        return isinstance(other, Matrix) and self.n == other.n and all(self.vals[i][j] == other.vals[i][j] for i in range(self.n) for j in range(self.n))
        

M = TypeVar('M', bound='Monoid')
class Monoid(Protocol):
    def __add__(self: M, other: M) -> M:
        ...

    @staticmethod
    def zero() -> M:
        ...

class IterableMonoid(Iterable, Monoid, Protocol):
    ...

class Path:
    def __init__(self, p=tuple()):
        self.p: Tuple[Edge] = p

    def __add__(self, other: 'Path') -> 'Path':
        return Path(self.p + other.p)

    def __iter__(self, *args, **kwargs):
        return self.p.__iter__(*args, **kwargs)

    @staticmethod
    def zero():
        return Path()

    def __repr__(self):
        return f'{self.p}'

    def __eq__(self, other):
        return set(self.p) == set(other.p)

    def __hash__(self) -> int:
        return frozenset(self.p).__hash__()


L = TypeVar('L', bound=IterableMonoid)
class LangSemiring(Generic[L]):
    # M = List[Edge]
    def __init__(self, vals: Set[L]):
        self.vals: Set[L] = vals

    def __add__(self, other: 'LangSemiring'):
        return LangSemiring(self.vals.union(other.vals))

    def __mul__(self, other: 'LangSemiring'):
        return LangSemiring(set(p + q for p, q in product(self.vals - other.vals, other.vals) if set(p).isdisjoint(set(q))))

    def __repr__(self):
        return repr(self.vals)

    def __len__(self):
        return len(self.vals)

    def __eq__(self, other):
        return self.vals == other.vals

    @staticmethod
    def zero():
        return LangSemiring(set())

    @staticmethod
    def one():
        return LangSemiring(set())



def adjacency_matrix_from_graph(graph: Graph[Node]) -> Tuple[Matrix[LangSemiring[Path]], List[Node]]:
    nodes = sorted(graph.keys())
    n = len(nodes)
    adj: Matrix[LangSemiring[Path]] = Matrix(LangSemiring[Path], n)
    

    for i in range(n):
        for j in range(n):
            v1 = nodes[i]
            v2 = nodes[j]
            if v2 in graph[v1]:
                adj.vals[i][j] = LangSemiring({Path((Edge(v1, v2),))}) # type: ignore
    return adj, nodes


def is_zero(m: Matrix):
    for i in range(m.n):
        for j in range(m.n):
            if m.vals[i][j] != m.mat.zero():
                return False
    return True