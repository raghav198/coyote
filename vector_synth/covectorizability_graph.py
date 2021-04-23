from ast_def import Var, Compiler, Op, fuzzer, Instr
from typing import Dict, List, Tuple
from similarity_heuristic import similarity, cache
from max_clique import BreaksetCalculator
from z3 import unsat


# exp = plus(times(Var('a'), Var('b')), times(
#     plus(Var('c'), Var('d')), plus(Var('x'), Var('y'))))

# print(exp)


def fully_connected(exp):
    def get_all_nodes(exp):
        if isinstance(exp, Var):
            return []
        return get_all_nodes(exp.lhs) + get_all_nodes(exp.rhs) + [exp]

    all_nodes = get_all_nodes(exp)
    connections = []
    for i in range(len(all_nodes)):
        for j in range(i + 1, len(all_nodes)):
            connections.append((all_nodes[i], all_nodes[j]))
    return connections


def traverse(base, cur, trace, on, connections):
    if isinstance(cur, Var) or cur == base:
        return

    if on:
        connections.remove((base, cur))
    if on and trace[0] == 0:
        traverse(
            base, cur.lhs, trace[1:], True, connections)
        traverse(
            base, cur.rhs, trace[1:], False, connections)
    elif on:
        traverse(
            base, cur.lhs, trace[1:], False, connections)
        traverse(
            base, cur.rhs, trace[1:], True, connections)
    else:
        traverse(
            base, cur.lhs, trace[1:], False, connections)
        traverse(
            base, cur.rhs, trace[1:], False, connections)


def prune_deps(node, exp, conns, trace=[]):
    if isinstance(node, Var):
        return
    traverse(node, exp, trace, True, conns)
    prune_deps(node.lhs, exp, conns, trace + [0])
    prune_deps(node.rhs, exp, conns, trace + [1])


def build_graph(exp, tag_lookup):
    # comp = Compiler(tag_lookup)
    # comp.compile(exp)

    similarity(exp, exp, tag_lookup)
    pairs = fully_connected(exp)
    prune_deps(exp, exp, pairs)
    connections = []
    weights = []
    for n1, n2 in pairs:
        connections.append((n1.tag, n2.tag))
        weights.append(cache.cache[n1.tag, n2.tag].pairs)

    return connections, weights


def get_breakset(exp, tag_lookup) -> Tuple[List[int], int]:
    # tag_lookup: Dict[int, Op] = dict()
    # comp = Compiler(tag_lookup)
    # comp.compile(exp)
    cache.clear()
    similarity(exp, exp, tag_lookup)
    pairs = fully_connected(exp)
    prune_deps(exp, exp, pairs)
    connections = []
    weights = []
    for n1, n2 in pairs:
        connections.append((n1.tag, n2.tag))
        weights.append(
            len(cache.cache[n1.tag, n2.tag].pairs))

    calc = BreaksetCalculator(connections, weights)
    breakset_idx, savings = calc.solve()
    breakset: List[Op] = []
    for i in breakset_idx:
        breakset.append(tag_lookup[i])

    return breakset_idx, savings
    # return breakset, savings


def code_lookup(code: List[Instr], tag: int, mod: List[int]):
    if tag in mod:
        return []

    lookup = []

    if code[tag].lhs.reg:
        lookup.extend(code_lookup(
            code, code[tag].lhs.val, mod))
    if code[tag].rhs.reg:
        lookup.extend(code_lookup(
            code, code[tag].rhs.val, mod))

    lookup.append(code[tag])
    return lookup


if __name__ == '__main__':

    VECTOR_PROGRAM = []

    exp = fuzzer(0.9)
    breakset_idx = []
    mod_list = []
    while True:
        print(exp)

        tag_lookup: Dict[int, Op] = dict()

        modded_exp = modOut(exp, mod_list)

        graph = build_graph(modded_exp, tag_lookup)

        calc = BreaksetCalculator(*graph)
        # breakset_idx: List[int] = []

        mod_list, (breakset_idx,
                   savings) = breakset_idx, calc.solve()
        breakset = []
        for i in breakset_idx:
            breakset.append(tag_lookup[i])

        # breakset, savings = get_breakset(exp)
        comp = Compiler({})
        print(f'Saving {savings} instructions')
        print('-' * 30)
        comp.compile(exp)
        for b in breakset:
            print(b)
            # comp.compile(b)
        print('-' * 30)

        # code = comp.code
        # code = sum([comp.code_lookup[b.tag]
        #             for b in breakset], [])

        code = sum(
            [code_lookup(comp.code, b.tag, mod_list) for b in breakset], [])

        print('\n'.join(map(str, code)))
        print('-' * 30)

        def convert(instr: Instr) -> TAC:
            return TAC(instr.dest.val, Atom(instr.lhs.val),
                       Atom(instr.rhs.val), instr.op)

        program = list(map(convert, code))

        for i in range(len(program)):
            print(f'Trying {i}...')
            schedule = get_vector_schedule(
                program, len(breakset), i)
            if schedule != unsat:
                break

        VECTOR_PROGRAM += build_vectorized_code(
            program,  *schedule, len(breakset))

        print('\n'.join(map(str, VECTOR_PROGRAM)))
