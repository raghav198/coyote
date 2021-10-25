from io import StringIO
from covectorizability_graph import build_graph
from recursive_similarity import MATCH_MUL
from sys import stderr
from typing import Dict, List, Set
from max_clique import BreaksetCalculator
from ast_def import Instr, plus, times, Compiler
from vector_compiler import vector_compile, lookup_code
from compile_convolution import get_matmul


def divide_stages(comp: Compiler, bkset_calc: BreaksetCalculator, input_groups: List[Set[str]] = [], log=stderr):
    quotients = []
    unused_outputs = set()

    # for each output of a stage, which previously unused outputs does it consume
    interstage_dicts: List[Dict[int, set]] = []
    # for each output of a stage, which stage intermediates does it consume
    intrastage_dicts: List[Dict[int, list]] = []

    program_stages: List[List[Instr]] = []

    max_warp = -1

    # Get an optimal set of breakpoints for this stage

    while True:
        if len(input_groups) > 0:
            cur_group = input_groups[0]
            del input_groups[0]

            bkset = []
            for instr in comp.code:
                if instr.op == '~' and instr.lhs.val in cur_group:
                    bkset.append(instr.dest.val)
        else:
            bkset, _ = bkset_calc.solve()  # get_breakset(expr, tag_lookup)
        if len(bkset) > max_warp:
            max_warp = len(bkset)

        if len(bkset) == 0:
            break

        bkset_calc.disallow(bkset)
        for b in bkset:
            bkset_calc.disallow(
                list(filter(lambda t: isinstance(t, int), comp.tag_lookup[b].subtags)))

        # Scalar program for this stage
        stage_code = sum([lookup_code(comp.code, bk, quotients)
                          for bk in bkset], [])
        print('-' * 30, file=log)
        print(bkset, file=log)
        print(quotients, file=log)
        print(stage_code, file=log)
        print('-' * 30, file=log)
        program_stages.append(stage_code)

        quotients += bkset
        intermediates = [instr.dest.val for instr in stage_code]

        unused_outputs |= set(bkset)

        stage_dict: Dict[int, set] = {}
        intrastage_dict: Dict[int, list] = {}

        for stage_output in bkset:
            equiv_class = set(
                filter(lambda l: l in unused_outputs, comp.tag_lookup[stage_output].subtags))
            stage_dict[stage_output] = equiv_class
            unused_outputs -= equiv_class

            intrastage_dict[stage_output] = list(
                filter(lambda l: l in intermediates, comp.tag_lookup[stage_output].subtags))

        interstage_dicts.append(stage_dict)
        intrastage_dicts.append(intrastage_dict)

    return program_stages, interstage_dicts, intrastage_dicts, max_warp


def get_3x3_determinant():
    c00, c01, c02, c10, c11, c12, c20, c21, c22 = get_matmul('a', 'b', 3, 3, 3)
    term1 = times(c00, plus(times(c11, c22), times(c12, c21)))
    term2 = times(c01, plus(times(c10, c22), times(c12, c20)))
    term3 = times(c02, plus(times(c10, c21), times(c11, c20)))
    determinant = plus(term1, plus(term2, term3))

    return determinant


def get_2x2_determinant():
    c00, c01, c10, c11 = get_matmul('a', 'b', 2, 2, 2)
    return plus(times(c00, c11), times(c10, c01))


def manually_compile_with_input_sets(comp: Compiler, log=stderr):
    # split the scalar program into stages
    bkset_calc = BreaksetCalculator(
        comp.target + 1, *build_graph(comp.exprs, log=log), rotate_penalty=MATCH_MUL, log=log)

    program_stages, interstage_deps, intrastage_deps, warp_size = divide_stages(
        comp, bkset_calc, input_groups=[{'a:0,0', 'a:0,1', 'a:1,0', 'a:1,1'}, {'b:0,0', 'b:0,1', 'b:1,0', 'b:1,1'}], log=log)

    for stage in program_stages:
        print('\n'.join(map(str, stage)))
        print('-' * 15)


if __name__ == '__main__':
    # exprs = [get_3x3_determinant()]
    exprs = [get_2x2_determinant()]
    # exprs = get_matmul('a', 'b', 3, 3, 3)
    input_groups = [{
        'a:0,0', 'a:0,1', 'a:0,2',
        'a:1,0', 'a:1,1', 'a:1,2',
        'a:2,0', 'a:2,1', 'a:2,2'}, {
            'b:0,0', 'b:0,1', 'b:0,2',
            'b:1,0', 'b:1,1', 'b:1,2',
            'b:2,0', 'b:2,1', 'b:2,2'}]
    c = Compiler({}, input_groups, allow_replicating=[])
    tag_list = [c.compile(expr) for expr in exprs]
    # for expr in exprs:
    #     c.compile(expr)

    scalar_code = '\n'.join(map(str, c.code))
    scalar_code = ' '.join(map(str, tag_list)) + '\n' + scalar_code
    print(scalar_code, file=open('outputs/determinant2x2/scal', 'w'))
    vectorized, width = vector_compile(c, log=StringIO())

    print(str(width) + '\n' + '\n'.join(vectorized), file=open('outputs/determinant2x2/vec', 'w'))
