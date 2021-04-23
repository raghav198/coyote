from typing import Any, Dict, Iterable, Tuple
from ast_def import *


class SimilarityTable:
    def __init__(self):
        self.cache = {}

    def __call__(self, estimator):
        def decorated(node1, node2, tag_lookup):
            if (node1.tag, node2.tag) not in self.cache:
                self.cache[node1.tag, node2.tag] = estimator(
                    node1, node2, tag_lookup)
            return self.cache[node1.tag, node2.tag]
        return decorated

    def clear(self):
        self.cache = {}


class VectorPack:
    def __init__(self, left: List[int] = [], right: List[int] = [],
                 pairs: List[Tuple[int, int]] = []):
        self.left = left
        self.right = right
        self.pairs = pairs

    def __repr__(self) -> str:
        return f'{self.left}; {self.right}; {self.pairs}'


def merge_pairs(p1: List[Tuple[Any, Any]], p2: List[Tuple[Any, Any]],
                mergeLeft=True) -> List[Tuple[Any, Any]]:
    def flip(seq: Iterable[Tuple[Any, Any]]) -> List[Tuple[Any, Any]]:
        if not seq:
            return []
        a, b = zip(*seq)
        return list(zip(b, a))

    pairs: Dict = {}

    if mergeLeft:
        for x, y in p1 + p2:
            if x not in pairs or pairs[x] > y:
                pairs[x] = y
        return list(pairs.items())
    else:
        for x, y in p1 + p2:
            if y not in pairs or pairs[y] > x:
                pairs[y] = x
        return list(flip(pairs.items()))


def combine(v1: VectorPack, v2: VectorPack, op: str, tag: int,
            tag_lookup: Dict[int, Op], joinLeft=True) -> VectorPack:
    v3 = VectorPack()
    if joinLeft:
        assert v1.left == v2.left
        v3.left = v1.left[:]
        v3.right = v1.right + v2.right + [tag]
    else:
        assert v1.right == v2.right
        v3.left = v1.left + v2.left + [tag]
        v3.right = v1.right[:]

    v3.pairs = merge_pairs(
        v1.pairs, v2.pairs, mergeLeft=joinLeft)

    tuple_index = 0 if joinLeft else 1
    latest_pair = max(list(zip(*v3.pairs))
                      [tuple_index]) if v3.pairs else -1

    pair_candidates = v3.left if joinLeft else v3.right
    for candidate_tag in pair_candidates:
        if candidate_tag > latest_pair and tag_lookup[candidate_tag].op == op:
            v3.pairs.append(
                (candidate_tag, tag) if joinLeft else (tag, candidate_tag))
            break
    return v3


def bottom(node: Expression) -> bool:
    return isinstance(node, Op) and isinstance(node.lhs, Var) and isinstance(node.rhs, Var)


def irreducible(node: Expression) -> bool:
    return bottom(node) or isinstance(node, Var)


cache = SimilarityTable()


@cache
def similarity(node1: Expression, node2: Expression, tag_lookup: Dict[int, Op]) -> VectorPack:
    def inst(node):
        return [] if isinstance(node, Var) else [node.tag]

    if bottom(node1) and bottom(node2):
        # make mypy happy
        assert (isinstance(node1, Op) and
                isinstance(node2, Op))

        return VectorPack([node1.tag], [node2.tag],
                          [(node1.tag, node2.tag)] if node1.op == node2.op else [])
    elif irreducible(node1) and irreducible(node2):
        # one of them has to be a Var, and the other either Var or Bottom
        return VectorPack(inst(node1), inst(node2), [])

    if not irreducible(node1):
        assert isinstance(node1, Op)
        # we have to recurse on node1
        lhs_sim = similarity(node1.lhs, node2, tag_lookup)
        rhs_sim = similarity(node1.rhs, node2, tag_lookup)
        ans = combine(lhs_sim, rhs_sim, node1.op,
                      node1.tag, tag_lookup, joinLeft=False)
        ans1 = ans

    if not irreducible(node2):
        assert isinstance(node2, Op)
        # we have to recurse on node2
        lhs_sim = similarity(node1, node2.lhs, tag_lookup)
        rhs_sim = similarity(node1, node2.rhs, tag_lookup)
        ans = combine(lhs_sim, rhs_sim, node2.op,
                      node2.tag, tag_lookup, joinLeft=True)
        ans2 = ans

    return ans


if __name__ == '__main__':
    e1 = fuzzer(0.8)
    e2 = fuzzer(0.8)

    tag_lookup: Dict[int, Op] = dict()

    comp = Compiler(tag_lookup)
    comp.compile(e1)
    comp.compile(e2)

    sim = similarity(e1, e2, tag_lookup)

    print(e1)
    print(e2)
    print('-' * 20)
    print('\n'.join(map(str, comp.code)))
    print('-' * 20)
    for x in sim.left:
        for y in sim.right:
            print(
                f'{x} with {y} saves {cache.cache[x, y].pairs}')
    print('=' * 30)
    print(f'e1 = {repr(e1)}\ne2 = {repr(e2)}')
