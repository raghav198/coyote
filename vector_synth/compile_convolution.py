from build_code import build_vector_program, place_output_lanes, propagate_lane_assigments
from typing import Dict, List, Set
from vectorize import VecInstr, synthesize_schedule
from ast_def import Atom, Instr, plus, times
from vector_compiler import Compiler, prepare_all, vector_compile, code_stats


def sum_all(summands):
    if len(summands) == 1:
        return summands[0]
    midpoint = len(summands) // 2
    return plus(sum_all(summands[:midpoint]), sum_all(summands[midpoint:]))


def get_convolution(width, height, ksize):
    summands = []
    for h in range(height):
        for w in range(width):
            for kh in range(ksize):
                for kw in range(ksize):
                    summands.append(
                        times(f'img({h+kh}, {w+kw})', f'f({kh}, {kw})'))

    return sum_all(summands)


def get_matmul(mat1, mat2, m, n, p):
    entries = []
    for i in range(m):
        for j in range(n):
            c_ij = []
            for k in range(p):
                c_ij.append(times(f'{mat1}:{i},{k}', f'{mat2}:{k},{j}'))
            entries.append(sum_all(c_ij))
    return entries


def fake_compile(program_stages: List[List[Instr]], interstage: List[Dict[int, Set]], intrastage: List[Dict[int, list]]):

    output_placement = place_output_lanes(interstage, 4)
    lanes = propagate_lane_assigments(output_placement, intrastage)

    vector_program: List[VecInstr] = []
    schedule = [0] * sum(map(len, program_stages))
    for stage in program_stages:
        stage_sched = synthesize_schedule(stage, 4)
        for s, i in zip(stage_sched, stage):
            schedule[i.dest.val] = s + len(vector_program)
        vector_program += build_vector_program(stage, lanes, stage_sched)

    return prepare_all(vector_program, interstage, lanes, schedule, 4)


def hardcoded_matmul():

    stage_a = [
        Instr(0, Atom('a00'), Atom('a00'), '~'),
        Instr(1, Atom('a01'), Atom('a01'), '~'),
        Instr(2, Atom('a10'), Atom('a10'), '~'),
        Instr(3, Atom('a11'), Atom('a11'), '~')
    ]

    stage_b = [
        Instr(4, Atom('b00'), Atom('b00'), '~'),
        Instr(5, Atom('b01'), Atom('b01'), '~'),
        Instr(6, Atom('b10'), Atom('b10'), '~'),
        Instr(7, Atom('b11'), Atom('b11'), '~')
    ]

    stage_1 = [
        Instr(8, Atom(0), Atom(4), '*'),
        Instr(9, Atom(1), Atom(6), '*'),
        Instr(10, Atom(8), Atom(9), '+'),
        Instr(11, Atom(0), Atom(5), '*'),
        Instr(12, Atom(1), Atom(7), '*'),
        Instr(13, Atom(11), Atom(12), '+'),
        Instr(14, Atom(2), Atom(4), '*'),
        Instr(15, Atom(3), Atom(6), '*'),
        Instr(16, Atom(14), Atom(15), '+'),
        Instr(17, Atom(2), Atom(5), '*'),
        Instr(18, Atom(3), Atom(7), '*'),
        Instr(19, Atom(17), Atom(18), '+')
    ]

    stage_2 = [
        Instr(20, Atom(10), Atom(19), '*'),
        Instr(21, Atom(13), Atom(16),  '*'),
        Instr(22, Atom(20), Atom(21), '+')
    ]

    inter_a = {0: set(), 1: set(), 2: set(), 3: set()}
    inter_b = {4: set(), 5: set(), 6: set(), 7: set()}
    inter_1 = {
        10: {0, 1, 4, 6},
        13: {0, 1, 5, 7},
        16: {2, 3, 4, 6},
        19: {2, 3, 5, 7}
    }
    inter_2 = {
        22: {10, 13, 16, 19}
    }

    intra_a = {0: set(), 1: set(), 2: set(), 3: set()}
    intra_b = {4: set(), 5: set(), 6: set(), 7: set()}
    intra_1 = {
        10: {8, 9},
        13: {11, 12},
        16: {14, 15},
        19: {17, 18}
    }
    intra_2 = {
        22: {20, 21}
    }

    print('\n'.join(fake_compile([stage_a, stage_b, stage_1, stage_2], [
          inter_a, inter_b, inter_1, inter_2], [intra_a, intra_b, intra_1, intra_2])))

    print('=' * 30)

    c00 = plus(times('a00', 'b00'), times('a01', 'b10'))
    c01 = plus(times('a00', 'b01'), times('a01', 'b11'))
    c10 = plus(times('a10', 'b00'), times('a11', 'b10'))
    c11 = plus(times('a10', 'b01'), times('a11', 'b11'))
    det = plus(times(c00, c11), times(c01, c10))

    # print(det)
    c = Compiler({})
    # c.compile(c00)
    # c.compile(c01)
    # c.compile(c10)
    # c.compile(c11)
    c.compile(det)
    print('\n'.join(map(str, c.code)))
    vector_code = vector_compile(c)
    print('\n'.join(vector_code))


if __name__ == '__main__':

    e1 = plus(times('a', 'b'), 'c')
    e2 = times(times('a', 'c'), plus('b', 'd'))
    e3 = plus('a', times('b', plus('c', times('d', 'e'))))

    print(e1)
    print(e2)
    print(e3)

    c = Compiler({})
    c.compile(e1)
    c.compile(e2)
    c.compile(e3)
    print('Scalar code:')
    print('\n'.join(map(str, c.code)))
    vector_code = vector_compile(c)

    print('Vector code:')
    print('\n'.join(vector_code))

    raise SystemExit()

    expr = get_convolution(5, 5, 3)
    comp = Compiler({})
    comp.compile(expr)
    scalar_code = list(map(str, comp.code))
    vector_code = vector_compile(comp)
    print('\n'.join(vector_code))

    print(f'Scalar stats: {code_stats(scalar_code)}')
    print(f'Vector stats: {code_stats(vector_code)}')
