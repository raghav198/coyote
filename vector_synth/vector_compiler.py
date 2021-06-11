from time import time

from pyrfc3339 import generate
from covectorizability_graph import build_graph, BreaksetCalculator
from ast_def import *
from typing import Dict
from vectorize import synthesize_schedule
from build_code import place_lanes, build_vector_program
from vectorize import VecInstr
from sys import stderr
from collections import defaultdict


seed(3)


def lookup_code(program: List[Instr], tag: int, modulus: List[int]) -> List[Instr]:
    """Find a subset of a scalar program thats used to compute a particular value relative to
    another set of values.
    @param program: Original scalar program, as a list of instructions. This is complete,
    so an index into the list has the corresponding tag
    @param tag: Tag of the final value for which we are producing a set of instructions
    @param modulus: List of tags of values. When looking up a program for `tag`,
    we assume that the tags in `modulus` are already available (and hence there is no need
    to include the instructions computing them)

    @return: A list of scalar instructions"""

    if tag in modulus:
        return []

    lookup = []
    if program[tag].lhs.reg:
        lookup.extend(lookup_code(program, program[tag].lhs.val, modulus))
    if program[tag].rhs.reg:
        lookup.extend(lookup_code(program, program[tag].rhs.val, modulus))
    lookup.append(program[tag])

    return lookup


def quotient_relative_expression(expr: Expression, modulus: List[int]) -> Expression:
    """Quotient out an expression by a list of subexpressions
    @param expr: The original expression
    @param modulus: A list of tags of subexpressions which get quotiented to an atom within `expr`

    @return: The quotiented expression"""

    if isinstance(expr, Var):
        return expr

    assert isinstance(expr, Op)
    if expr.tag in modulus:
        return Var(f'tmp{expr.tag}')

    return Op(expr.op, quotient_relative_expression(expr.lhs, modulus),
              quotient_relative_expression(expr.rhs, modulus))


def divide_stages(comp: Compiler, bkset_calc: BreaksetCalculator, root_tag: int):
    quotients = []
    unused_outputs = set()

    # for each output of a stage, which previously unused outputs does it consume
    interstage_dicts: List[Dict[int, set]] = []
    # for each output of a stage, which stage intermediates does it consume
    intrastage_dicts: List[Dict[int, list]] = []

    program_stages: List[List[Instr]] = []

    max_warp = -1

    # Get an optimal set of breakpoints for this stage
    final_stage = False
    while not final_stage:
        bkset, _ = bkset_calc.solve()  # get_breakset(expr, tag_lookup)
        if len(bkset) > max_warp:
            max_warp = len(bkset)

        if len(bkset) == 0:
            final_stage = True
            bkset = [root_tag]
        bkset_calc.disallow(bkset)
        for b in bkset:
            bkset_calc.disallow(
                list(filter(lambda t: isinstance(t, int), comp.tag_lookup[b].subtags)))

        # Scalar program for this stage
        stage_code = sum([lookup_code(comp.code, bk, quotients) for bk in bkset], [])
        print('-' * 30, file=stderr)
        print(bkset, file=stderr)
        print(quotients, file=stderr)
        print(stage_code, file=stderr)
        print('-' * 30, file=stderr)
        """ TODO: This shows that %20 and %21 are both being added to the breakset,
        despite dependency %21 <-- %20 """
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


def vector_compile(expr):
    tag_lookup: Dict[int, Op] = {}
    comp = Compiler(tag_lookup)
    comp.compile(expr)

    # split the scalar program into stages
    bkset_calc = BreaksetCalculator(*build_graph(expr, tag_lookup))
    program_stages, interstage_deps, intrastage_deps, warp_size = divide_stages(
        comp, bkset_calc, expr.tag)

    # optimal lane placement based on interstage and intrastage dependences
    lanes = place_lanes(interstage_deps, intrastage_deps)

    # build vector schedule
    vector_program: List[VecInstr] = []
    schedule = [0] * len(comp.code)
    for stage in program_stages:
        stage_sched = synthesize_schedule(stage, warp_size)
        for s, i in zip(stage_sched, stage):
            schedule[i.dest.val] = s + len(vector_program)
        vector_program += build_vector_program(stage, lanes, stage_sched)

    # compute all the rotation/blending
    shifts = {}
    for stage_deps in interstage_deps[1:]:  # first stage doesn't have any inputs
        for out, inputs in stage_deps.items():
            for inp in inputs:
                shift_amt = (lanes[out] - lanes[inp]) % warp_size
                if shift_amt == 0:
                    continue
                shifts[inp] = shift_amt

    temp_num = 0
    temp_shift = 0
    shifted_names = {}
    generated_code = []

    for i, instr in enumerate(vector_program):
        keys_to_shift = []  # which keys need shifted
        shifts_used = []
        # queue up all the shifting we need to do for this instruction
        for key, shift in shifts.items():
            if key in [dest.val for dest in instr.dest]:
                if shift in shifts_used:
                    continue
                shifts_used.append(shift)
                keys_to_shift.append(key)
                shifted_names[key] = f'__s{temp_shift}'
                temp_shift += 1

        # bitvectors for blending regs from multiple sources
        left_blend = defaultdict(lambda: [0] * warp_size)
        right_blend = defaultdict(lambda: [0] * warp_size)
        # where to blend in constants
        left_constants = [0] * len(instr.left)
        right_constants = [0] * len(instr.right)

        # collect all the sources to be blended for left operand
        for j, symbol in enumerate(instr.left):
            if symbol != Atom(BLANK_SYMBOL) and symbol.reg:
                if symbol.val in shifted_names:
                    src_vec = shifted_names[symbol.val]
                else:
                    src_vec = f'__v{schedule[symbol.val]}'

                left_blend[src_vec][j] = 1
            elif symbol != Atom(BLANK_SYMBOL):
                left_constants[j] = symbol.val

        # collect all the sources to be blended for right operand
        for j, symbol in enumerate(instr.right):
            if symbol != Atom(BLANK_SYMBOL) and symbol.reg:
                if symbol.val in shifted_names:
                    src_vec = shifted_names[symbol.val]
                else:
                    src_vec = f'__v{schedule[symbol.val]}'

                right_blend[src_vec][j] = 1
            elif symbol != Atom(BLANK_SYMBOL):
                right_constants[j] = symbol.val

        if any(x != 0 for x in left_constants):
            generated_code.append(f'__t{temp_num} = [{", ".join(map(str, left_constants))}]')
            left_blend[f'__t{temp_num}'] = [int(x != 0) for x in left_constants]
            temp_num += 1

        if any(x != 0 for x in right_constants):
            generated_code.append(f'__t{temp_num} = [{", ".join(map(str, right_constants))}]')
            right_blend[f'__t{temp_num}'] = [int(x != 0) for x in right_constants]
            temp_num += 1

        if len(left_blend.keys()) > 1:
            blend_line = ', '.join([f'{v}@{"".join(map(str, m))}' for v, m in left_blend.items()])
            generated_code.append(f'__t{temp_num} = blend({blend_line})')
            instr.left = f'__t{temp_num}'
            temp_num += 1
        elif len(left_blend.keys()) == 1:
            instr.left = f'{list(left_blend.keys())[0]}'

        if len(right_blend.keys()) > 1:
            blend_line = ', '.join([f'{v}@{"".join(map(str, m))}' for v, m in right_blend.items()])
            generated_code.append(f'__t{temp_num} = blend({blend_line})')
            instr.right = f'__t{temp_num}'
            temp_num += 1
        elif len(right_blend.keys()) == 1:
            instr.right = f'{list(right_blend.keys())[0]}'

        instr.dest = f'__v{i}'
        generated_code.append(f'{instr}')

        for key in keys_to_shift:
            shift = shifts[key]
            if shift < 0:
                generated_code.append(f'{shifted_names[key]} = {instr.dest} << {-shift}')
            elif shift > 0:
                generated_code.append(f'{shifted_names[key]} = {instr.dest} >> {shift}')

    return generated_code


if __name__ == '__main__':
    # expr = times(times(times('d', 'b'), plus('g', times('w', 'p'))),
    #              times(times('e', 'x'), plus(plus(plus('h', 'n'), 'q'), 'o')))
    expr = fuzzer(0.9)
    print(expr)
    code = vector_compile(expr)
    print('\n'.join(code))
    raise SystemExit()

# if __name__ == '__main__':
    # Generate a random expression for testing
    # expr = fuzzer(0.85)

    # expr = times(times(times('d', 'b'), plus('g', times('w', 'p'))),
    #              times(times('e', 'x'), plus(plus(plus('h', 'n'), 'q'), 'o')))

    # print(expr)

    # # Compile to a scalar program
    # tag_lookup: Dict[int, Op] = {}
    # comp = Compiler(tag_lookup)
    # comp.compile(expr)
    # code = comp.code

    # print('=' * 30)
    # print('ORIGINAL SCALAR PROGRAM:')
    # print('\n'.join(map(str, code)))
    # print('=' * 30)

    # start = time()

    # bkset_calc = BreaksetCalculator(*build_graph(expr, tag_lookup))

    # program_stages, interstage_dicts, intrastage_dicts, max_warp = divide_stages(
    #     comp, bkset_calc, expr.tag)

    # instr_lanes = place_lanes(interstage_dicts, intrastage_dicts)

    # vector_program: List[VecInstr] = []
    # total_schedule = [0] * len(code)

    # for stage in program_stages:
    #     sched = synthesize_schedule(stage, max_warp)
    #     for s, i in zip(sched, stage):
    #         total_schedule[i.dest.val] = s + len(vector_program)
    #     vector_program += build_vector_program(stage, instr_lanes, sched)

    # # SHUFFLE
    # print('=' * 30)
    # print('SHIFTS:')
    # shift_dict = {}
    # for stage_dict in interstage_dicts[1:]:
    #     for key, val in stage_dict.items():
    #         for i in val:
    #             shift_amt = (instr_lanes[key] - instr_lanes[i]) % max_warp
    #             if shift_amt == 0:
    #                 continue
    #             # if instr_lanes[key] > instr_lanes[i]:
    #             #     print("%"+str(i)+" >> "+str(instr_lanes[key] - instr_lanes[i]))
    #             #     shift_dict[i] = instr_lanes[key] - instr_lanes[i]
    #             # elif instr_lanes[key] < instr_lanes[i]:
    #             #     print("%"+str(i)+" << "+str(instr_lanes[i] - instr_lanes[key]))
    #             #     shift_dict[i] = instr_lanes[key] - instr_lanes[i]
    #             print(f'%{i} >> {shift_amt}')
    #             shift_dict[i] = shift_amt

    # temp = 0
    # temp_shift = 0
    # shift_key = {}
    # vec_prog = []

    # print('=' * 30)
    # print('FINAL VECTOR PROGRAM:')
    # print('\n'.join(map(str, vector_program)))
    # print('=' * 30)

    # for i, vec_instr in enumerate(vector_program):

    #     keys_to_shift = []
    #     shifts_used = []
    #     for key, shift in shift_dict.items():
    #         if key in [dest.val for dest in vec_instr.dest]:
    #             if shift in shifts_used:
    #                 continue
    #             shifts_used.append(shift)
    #             keys_to_shift.append(key)
    #             shift_key[key] = f's{temp_shift}'
    #             temp_shift += 1

    #     left_blend = defaultdict(lambda: [0] * max_warp)
    #     right_blend = defaultdict(lambda: [0] * max_warp)

    #     left_constants = [0] * len(vec_instr.left)
    #     for j, symbol in enumerate(vec_instr.left):
    #         if symbol != Atom(BLANK_SYMBOL) and symbol.reg:
    #             if symbol.val in shift_key:
    #                 src_vec = shift_key[symbol.val]
    #             else:
    #                 src_vec = f'v{total_schedule[symbol.val]}'

    #             left_blend[src_vec][j] = 1
    #         elif symbol != Atom(BLANK_SYMBOL):
    #             left_constants[j] = symbol.val

    #     right_constants = [0] * len(vec_instr.right)
    #     for j, symbol in enumerate(vec_instr.right):
    #         if symbol != Atom(BLANK_SYMBOL) and symbol.reg:
    #             if symbol.val in shift_key:
    #                 src_vec = shift_key[symbol.val]
    #             else:
    #                 src_vec = f'v{total_schedule[symbol.val]}'

    #             right_blend[src_vec][j] = 1
    #         elif symbol != Atom(BLANK_SYMBOL):
    #             right_constants[j] = symbol.val

    #     if any(x != 0 for x in left_constants):
    #         print(f't{temp} = [{", ".join(map(str, left_constants))}]')
    #         left_blend[f't{temp}'] = [int(x != 0) for x in left_constants]
    #         temp += 1

    #     if any(x != 0 for x in right_constants):
    #         print(f't{temp} = [{", ".join(map(str, right_constants))}]')
    #         right_blend[f't{temp}'] = [int(x != 0) for x in right_constants]
    #         temp += 1

    #     if len(left_blend.keys()) > 1:
    #         blend_line = ', '.join([f'{v}@{"".join(map(str, m))}' for v, m in left_blend.items()])
    #         print(f't{temp} = blend({blend_line})')
    #         vec_instr.left = f't{temp}'
    #         temp += 1
    #     elif len(left_blend.keys()) == 1:
    #         vec_instr.left = f'{list(left_blend.keys())[0]}'

    #     if len(right_blend.keys()) > 1:
    #         blend_line = ', '.join([f'{v}@{"".join(map(str, m))}' for v, m in right_blend.items()])
    #         print(f't{temp} = blend({blend_line})')
    #         vec_instr.right = f't{temp}'
    #         temp += 1
    #     elif len(right_blend.keys()) == 1:
    #         vec_instr.right = f'{list(right_blend.keys())[0]}'

    #     # print(vec_instr.dest, dict(left_blend), dict(right_blend))
    #     dest_val = vec_instr.dest
    #     vec_instr.dest = f'v{i}'
    #     print(f'{vec_instr}')

    #     for key in keys_to_shift:
    #         shift = shift_dict[key]
    #         if shift < 0:
    #             print(f'{shift_key[key]} =  {vec_instr.dest} <<  {-shift}')
    #         elif shift > 0:
    #             print(f'{shift_key[key]} =  {vec_instr.dest} >> {shift}')

    #     vec_prog.append(vec_instr)

    # end = time()

    # print('=' * 30)
    # print('STAGE DICTIONARIES:')
    # print(interstage_dicts)
    # print(intrastage_dicts)

    # print(f'Synthesized vector program in {int(1000 * (end - start))} ms')
    # # print(f'Reduced {len(code)} scalar instructions to approx {vector_cost_estimate}')
