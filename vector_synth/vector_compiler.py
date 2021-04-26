from time import time
from covectorizability_graph import build_graph, BreaksetCalculator
from ast_def import *
from typing import Dict
from vectorize import synthesize_schedule
from build_code import place_lanes, build_vector_program
from vectorize import VecInstr
from collections import defaultdict


seed(5)


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


def divide_stages(code, bkset_calc):
    quotients = []
    unused_outputs = set()

    interstage_dicts = []
    intrastage_dicts = []

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
            bkset = [expr.tag]
        bkset_calc.disallow(bkset)
        for b in bkset:
            bkset_calc.disallow(list(filter(lambda t: isinstance(t, int), tag_lookup[b].subtags)))

        # Scalar program for this stage
        stage_code = sum([lookup_code(code, bk, quotients) for bk in bkset], [])
        program_stages.append(stage_code)

        quotients += bkset
        intermediates = [instr.dest.val for instr in stage_code]

        unused_outputs |= set(bkset)

        stage_dict = {}
        intrastage_dict = {}

        for stage_output in bkset:
            equiv_class = set(
                filter(lambda l: l in unused_outputs, tag_lookup[stage_output].subtags))
            stage_dict[stage_output] = equiv_class
            unused_outputs -= equiv_class

            intrastage_dict[stage_output] = list(
                filter(lambda l: l in intermediates, tag_lookup[stage_output].subtags))

        interstage_dicts.append(stage_dict)
        intrastage_dicts.append(intrastage_dict)

    return program_stages, interstage_dicts, intrastage_dicts, max_warp


if __name__ == '__main__':
    # Generate a random expression for testing
    expr = fuzzer(0.9)
    print(expr)

    # Compile to a scalar program
    tag_lookup: Dict[int, Op] = {}
    comp = Compiler(tag_lookup)
    comp.compile(expr)
    code = comp.code

    print('=' * 30)
    print('ORIGINAL SCALAR PROGRAM:')
    print('\n'.join(map(str, code)))
    print('=' * 30)

    start = time()

    bkset_calc = BreaksetCalculator(*build_graph(expr, tag_lookup))

    program_stages, interstage_dicts, intrastage_dicts, max_warp = divide_stages(code, bkset_calc)

    instr_lanes = place_lanes(interstage_dicts, intrastage_dicts)

    vector_program: List[VecInstr] = []
    total_schedule = [0] * len(code)

    for stage in program_stages:
        sched = synthesize_schedule(stage, max_warp)
        for s, i in zip(sched, stage):
            total_schedule[i.dest.val] = s + len(vector_program)
        vector_program += build_vector_program(stage, instr_lanes, sched)

    #SHUFFLE
    print('=' * 30)
    print('SHIFTS:')
    shift_dict = {}
    for stage_dict in interstage_dicts[1:]:
        for key,val in stage_dict.items():
            for i in val:
                if instr_lanes[key] > instr_lanes[i]:
                    print("%"+str(i)+" >> "+str(instr_lanes[key] - instr_lanes[i]))
                    shift_dict[i] = instr_lanes[key] - instr_lanes[i]
                elif instr_lanes[key] < instr_lanes[i]:
                    print("%"+str(i)+" << "+str(instr_lanes[i] - instr_lanes[key]))
                    shift_dict[i] = instr_lanes[key] - instr_lanes[i]



    temp = 0
    temp_shift = 0
    shift_key = {}
    vec_prog= []
    for i, vec_instr in enumerate(vector_program):

        # left_blends = set()
        # right_blends = set()

        # left_lanes = [0] * max_warp
        # right_lanes = [0] * max_warp

        for key, shift in shift_dict.items():
            if key in [dest.val for dest in vec_instr.dest] and shift < 0:
                print(f's{temp_shift} =  {vec_instr.dest} <<  {-shift}')
                shift_key[key] = f's{temp_shift}'
                temp_shift += 1

            elif key in [dest.val for dest in vec_instr.dest] and shift > 0:
                print(f's{temp_shift} =  {vec_instr.dest} >> {shift}')
                shift_key[key] = f's{temp_shift}'
                temp_shift += 1


        for key,val in shift_key.items():
            if key in [left.val for left in vec_instr.left]:
                vec_instr.left = shift_key[key]
            elif key in [right.val for right in vec_instr.right]:
                vec_instr.right = shift_key[key]
      
        left_blend = defaultdict(lambda: [0] * max_warp)
        right_blend = defaultdict(lambda: [0] * max_warp)

        for symbol in vec_instr.left:
            if symbol != Atom(BLANK_SYMBOL) and symbol.reg:

                left_blend[total_schedule[symbol.val]][instr_lanes[symbol.val]] = 1

                # left_blends |= {total_schedule[symbol.val]}
                # left_lanes[instr_lanes[symbol.val]] = 1
        for symbol in vec_instr.right:
            if symbol != Atom(BLANK_SYMBOL) and symbol.reg:
                # right_blends |= {total_schedule[symbol.val]}
                # right_lanes[instr_lanes[symbol.val]] = 1
                right_blend[total_schedule[symbol.val]][instr_lanes[symbol.val]] = 1

        if len(left_blend.keys()) > 1:
            blend_line = ', '.join([f'v{v}@{"".join(map(str, m))}' for v, m in left_blend.items()])
            print(f't{temp} = blend({blend_line})')
            vec_instr.left = f't{temp}'
            temp += 1
        elif len(left_blend.keys()) == 1:
            vec_instr.left = f'v{list(left_blend.keys())[0]}'

        if len(right_blend.keys()) > 1:
            blend_line = ', '.join([f'v{v}@{"".join(map(str, m))}' for v, m in right_blend.items()])
            print(f't{temp} = blend({blend_line})')
            vec_instr.right = f't{temp}'
            temp += 1
        elif len(right_blend.keys()) == 1:
            vec_instr.right = f'v{list(right_blend.keys())[0]}'
                      

        # print(vec_instr.dest, dict(left_blend), dict(right_blend))
        dest_val = vec_instr.dest
        vec_instr.dest = f'v{i}'
        print(f'{vec_instr}')
        vec_prog.append(vec_instr)


    end = time()

    print('=' * 30)
    print('STAGE DICTIONARIES:')
    print(interstage_dicts)
    print(intrastage_dicts)


    print('=' * 30)
    print('FINAL VECTOR PROGRAM:')
    print('\n'.join(map(str, vector_program)))
    print('=' * 30)


    print(f'Synthesized vector program in {int(1000 * (end - start))} ms')
    # print(f'Reduced {len(code)} scalar instructions to approx {vector_cost_estimate}')

