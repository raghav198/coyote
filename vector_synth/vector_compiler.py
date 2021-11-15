from hypergraph_coloring import place_lanes_hypergraph_method
from manual_lane_placement import place_lanes_manually, place_lanes_piecewise
from covectorizability_graph import build_graph
from max_clique import BreaksetCalculator
from ast_def import *
from typing import Dict, Tuple
from vectorize import synthesize_schedule, VecInstr
from build_code import place_output_lanes, build_vector_program, propagate_lane_assigments, place_lanes
from sys import stderr
from collections import defaultdict
from recursive_similarity import MATCH_MUL
from numberTreeGenerator import treeGenerator


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
        lookup.extend(lookup_code(program, int(program[tag].lhs.val), modulus))
    if program[tag].rhs.reg:
        lookup.extend(lookup_code(program, int(program[tag].rhs.val), modulus))
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


def divide_stages(comp: Compiler, bkset_calc: BreaksetCalculator, log=stderr):
    quotients = []
    unused_outputs = set()

    all_output_dependencies: Dict[int, set] = {}

    # for each output of a stage, which previously unused outputs does it consume
    interstage_dicts: List[Dict[int, set]] = []
    # for each output of a stage, which stage intermediates does it consume
    intrastage_dicts: List[Dict[int, list]] = []

    program_stages: List[List[Instr]] = []

    max_warp = -1

    # Get an optimal set of breakpoints for this stage

    input_groups = comp.input_groups[:]

    while True:
        if len(input_groups) > 0:
            cur_group = input_groups[0]
            del input_groups[0]

            bkset: List[int] = []
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
        stage_code: List[Instr] = sum([lookup_code(comp.code, int(bk), quotients)
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
            # print(f'Dealing with stage output {stage_output}')
            # print(f'All outputs: {unused_outputs}')
            # print(f'Subtags: {comp.tag_lookup[stage_output].subtags}')
            equiv_class = set(comp.tag_lookup[stage_output].subtags).intersection(unused_outputs)
            # print(f'So far, equiv class is {equiv_class}')
            actual_equiv_class = equiv_class.copy()
            for val in equiv_class:
                actual_equiv_class -= all_output_dependencies[val]
            stage_dict[stage_output] = actual_equiv_class
            # print(f'Setting dependencies for this one to {actual_equiv_class}')
            all_output_dependencies[stage_output] = actual_equiv_class
            intrastage_dict[stage_output] = list(set(intermediates).intersection(set(comp.tag_lookup[stage_output].subtags)))
            # tags_computed_so_far.add(stage_output)


        # for stage_output in bkset:
        #     print(f'Dealing with stage output {stage_output}')
        #     print(f'Outputs unused so far: {unused_outputs}')
        #     print(f'All subtags: {comp.tag_lookup[stage_output].subtags}')
        #     # equiv_class = set(instr.dest.val for instr in stage_code).intersection(unused_outputs)
        #     equiv_class = set(
        #         filter(lambda l: l in unused_outputs, comp.tag_lookup[stage_output].subtags))
        #     print(f'Equivalence class of prior stage outputs being put in here: {equiv_class}')
        #     stage_dict[stage_output] = equiv_class
        #     unused_outputs -= equiv_class

        #     intrastage_dict[stage_output] = list(
        #         filter(lambda l: l in intermediates, comp.tag_lookup[stage_output].subtags))

        interstage_dicts.append(stage_dict)
        intrastage_dicts.append(intrastage_dict)

    return program_stages, interstage_dicts, intrastage_dicts, max_warp


def vector_compile(comp: Compiler, log=stderr):
    # tag_lookup: Dict[int, Op] = {}
    # comp = Compiler(tag_lookup)
    # comp.compile(expr)

    # split the scalar program into stages
    bkset_calc = BreaksetCalculator(
        comp.target + 1, *build_graph(comp.exprs, log=log), rotate_penalty=MATCH_MUL, log=log)
    program_stages, interstage_deps, intrastage_deps, warp_size = divide_stages(
        comp, bkset_calc, log=log)

    # optimal lane placement based on interstage and intrastage dependences
    print(interstage_deps, file=log)
    print(f'{len(interstage_deps)} stages')
    # output_placement = place_output_lanes(interstage_deps, warp_size)
    print(interstage_deps)
    print(warp_size)
    # raise SystemExit()




    # output_placement = place_lanes_piecewise(interstage_deps, warp_size)
    # output_placement = place_lanes_manually(interstage_deps, warp_size)
    output_placement = place_lanes_hypergraph_method(interstage_deps, warp_size)
    print(output_placement)
    warp_size = max(output_placement.values()) + 1
    print(f'Placed all stage outputs: {output_placement}, new warp size is {warp_size}')
    lanes = propagate_lane_assigments(output_placement, intrastage_deps)
    # lanes = place_lanes(interstage_deps, intrastage_deps, warp_size)

    # build vector schedule
    vector_program: List[VecInstr] = []
    schedule = [0] * len(comp.code)
    for stage in program_stages:
        # stage_sched = synthesize_schedule_iterative_refine(stage)
        stage_sched = synthesize_schedule(stage, warp_size, log=log)
        # stage_sched = synthesize_schedule(stage, warp_size, log=log)
        for s, i in zip(stage_sched, stage):
            schedule[i.dest.val] = s + len(vector_program)
        vector_program += build_vector_program(stage, lanes, stage_sched, log=log)

    active_lanes = [[] for _ in range(max(schedule) + 1)]
    for instr in comp.code:
        active_lanes[schedule[instr.dest.val]].append(lanes[instr.dest.val])
    # print(f'Active lanes: {active_lanes}')
    inv_schedule = [[-1] * (max(lanes) + 1) for _ in range(max(schedule) + 1)]
    for instr in comp.code:
        inv_schedule[schedule[instr.dest.val]][lanes[instr.dest.val]] = instr.dest.val

    print('\n'.join(map(str, comp.code)))

    print(f'Overall schedule: {inv_schedule}')
    print(f'Overall lanes: {lanes}')
    return prepare_all(vector_program, interstage_deps, intrastage_deps, lanes, schedule, warp_size), warp_size


def prepare_all(vector_program: List[VecInstr], interstage_deps: List[Dict[int, Set[int]]], intrastage_deps: List[Dict[int, List[int]]], lanes: List[int], schedule: List[int], warp_size: int):
    """
    interstage_deps: List[Dict[int, Set[int]]] ==> i: dict for stage i = (stage output reg -> set of prior stage input regs it consumes)
    intrastage_deps: List[Dict[int, List[int]]] ==> i: dict for stage i = (stage output reg -> list of stage intermediates)
    lanes: List[int] ==> i: lane # for reg i
    schedule: List[int] ==> i: vector # for reg i
    """


    shift_amounts_needed: Dict[int, Dict[int, int]] = defaultdict(lambda: defaultdict(lambda: 0)) # producer reg -> (consumer reg -> shift needed to line them up)
    for stage_dict, intermediates in zip(interstage_deps, intrastage_deps):
        for consumer, producers in stage_dict.items():
            for producer in producers:
                shift_amount = (lanes[consumer] - lanes[producer]) % warp_size
                shift_amounts_needed[producer][consumer] = shift_amount
                for intermediate in intermediates[consumer]:
                    shift_amounts_needed[producer][intermediate] = shift_amount
                # if producer in shift_amounts_needed:
                #     shift_amounts_needed[producer][consumer] = shift_amount
                # else:
                #     shift_amounts_needed[producer] = {consumer: shift_amount}

    shifted_vectors: Dict[Tuple[int, int], str] = {} # (register, shift amount) -> name of shifted vector
    amount_shifted: Dict[str, int] = {} # name of vector -> amount it has been rotated
    shift_temp = 0 # for creating new shifted vectors
    cur_temp = 0 # for creating temporaries
    generated_code: List[str] = []
    for i, instr in enumerate(vector_program):
        shifted_names: Dict[int, str] = {} # shift amount -> name of shifted vector [this is just specific to the current vector instruction]
        shifts_performed: List[int] = [] # what shifts are already queued up for this vector instruction?

        for dest in instr.dest: # for each register produced by this instruction
            if dest.val not in shift_amounts_needed:
                continue
            all_shifts = set(shift_amounts_needed[dest.val].values()) # all the amounts dest.val needs to be shifted by
            for shift in all_shifts:
                if shift == 0:
                    continue
                if shift not in shifts_performed:
                    # record that __v{i} is being shifted this amount
                    shifts_performed.append(shift)

                    # remember the name given to __v{i} >> {shift}
                    shifted_names[shift] = f'__s{shift_temp}'
                    amount_shifted[f'__s{shift_temp}'] = shift
                    shift_temp += 1
                # record which __s vector to use in order to access {dest.val} shifted by {shift}
                shifted_vectors[dest.val, shift] = shifted_names[shift]

        # which lanes to blend in constants
        def get_blends_and_constants(operands: List[Atom], dests: List[Atom]):
            # print(f'There are {len(operands)} operands and the warp size is {warp_size}')
            blend_masks: Dict[str, List[int]] = defaultdict(lambda: [0] * warp_size) # vector name -> bitvector mask needed for blends
            constants: List[Union[str, int]] = [0] * len(operands)

            for j, symbol in enumerate(operands):
                if symbol != Atom(BLANK_SYMBOL) and symbol.reg:
                    assert isinstance(symbol.val, int)
                    # find which source vec to get lane j of the left operand from
                    if symbol.val in shift_amounts_needed:
                        # its an output from a previous stage if its in the dictionary
                        shift_amount = shift_amounts_needed[symbol.val][dests[j].val]
                    else:
                        # its a temporary from this stage, no need to shift anyway
                        shift_amount = 0

                    if shift_amount == 0:
                        # no shift necessary, use the vector directly
                        src_vec = f'__v{schedule[symbol.val]}'
                    else:
                        # its been shifted, get the name of the shifted vector
                        src_vec = shifted_vectors[symbol.val, shift_amount]
                    blend_masks[src_vec][j] = 1
                elif symbol != Atom(BLANK_SYMBOL):
                    constants[j] = symbol.val

            return blend_masks, constants

        # print(shifted_vectors)
        left_blend, left_constants = get_blends_and_constants(instr.left, instr.dest)
        right_blend, right_constants = get_blends_and_constants(instr.right, instr.dest)

        if any(x != 0 for x in left_constants):
            generated_code.append(f'__t{cur_temp} = [{", ".join(map(str, left_constants))}]')
            left_blend[f'__t{cur_temp}'] = [int(x != 0) for x in left_constants]
            cur_temp += 1

        if any(x != 0 for x in right_constants):
            generated_code.append(f'__t{cur_temp} = [{", ".join(map(str, right_constants))}]')
            right_blend[f'__t{cur_temp}'] = [int(x != 0) for x in right_constants]
            cur_temp += 1

        if len(left_blend.keys()) > 1:
            # we need to emit a blend
            blend_line = ', '.join([f'{v}@{"".join(map(str, m))}' for v, m in left_blend.items()])
            generated_code.append(f'__t{cur_temp} = blend({blend_line})')
            instr.left = f'__t{cur_temp}'
            cur_temp += 1
        elif len(left_blend.keys()) == 1:
            # no blend necessary, just grab it directly
            instr.left = f'{list(left_blend.keys())[0]}'

        if len(right_blend.keys()) > 1:
            # we need to emit a blend
            blend_line = ', '.join([f'{v}@{"".join(map(str, m))}' for v, m in right_blend.items()])
            generated_code.append(f'__t{cur_temp} = blend({blend_line})')
            instr.right = f'__t{cur_temp}'
            cur_temp += 1
        elif len(right_blend.keys()) == 1:
            # no blend necessary, just grab it directly
            instr.right = f'{list(right_blend.keys())[0]}'

        instr.dest = f'__v{i}'
        generated_code.append(f'{instr}')

        for shift_amt, shifted_name in shifted_names.items():
            generated_code.append(f'{shifted_name} = {instr.dest} >> {shift_amt}')



    peepholes = [push_out_rotates, remove_repeated_ops]
    for peephole in peepholes:
        generated_code = peephole(generated_code)
    return generated_code

def push_out_rotates(generated_code: List[str]) -> List[str]:
    import re
    # Collect metadata
    lines_used: Dict[str, List[int]] = {} # variable -> list of line nums it gets used on
    defined_vars: Dict[str, int] = {} # variable -> line num its defined on
    rotation_amount: Dict[str, int] = {} # variable -> amount its been rotated
    original_var: Dict[str, str] = {} # rotated variable -> unshifted version of it
    next_v = 0
    for i, line in enumerate(generated_code):
        lhs, rhs = line.split(' = ')
        if lhs.startswith('__v'):
            next_v += 1
        for v in defined_vars:
            if v in rhs:
                lines_used[v].append(i)
        defined_vars[lhs] = i
        lines_used[lhs] = []
        if '>>' in rhs:
            orig, amt = rhs.split(' >> ')
            rotation_amount[lhs] = amt
            original_var[lhs] = orig

    # push rotations down when possible
    for i, line in enumerate(generated_code):
        lhs, rhs = line.split(' = ')
        p = re.split(' (\+|-|\*) ', rhs)
        if len(p) == 3:
            x, _, y = p
            if x in rotation_amount and y in rotation_amount and rotation_amount[x] == rotation_amount[y]:
                if len(lines_used[x]) == 1 and len(lines_used[y]) == 1:
                    # remove both rotation lines
                    generated_code[defined_vars[x]] = ''
                    generated_code[defined_vars[y]] = ''

                    # add a rotate after this line
                    generated_code[i] = generated_code[i].replace(
                                                x, original_var[x]).replace(
                                                y, original_var[y]).replace(
                                                lhs, f'__v{next_v}'
                                                ) + \
                                                f'\n{lhs} = __v{next_v} >> {rotation_amount[x]}'
                    next_v += 1

    print(next_v)
    return list(filter(None, '\n'.join(generated_code).split('\n')))


def remove_repeated_ops(generated_code: List[str]) -> List[str]:
    import re
    computation: Dict[str, str] = {} # expression -> variable storing that expression (backwards of assignment)
    remap: Dict[str, str] = {} # variable -> variable to use instead of it
    for i, line in enumerate(generated_code):
        print(f'{i}: {line}')
        lhs, rhs = line.split(' = ')

        for v in remap:
            rhs = re.sub(rf'\b{v}\b', remap[v], rhs)
            # rhs = rhs.replace(v, remap[v])

        if rhs in computation:
            generated_code[i] = ''
            remap[lhs] = computation[rhs]
        else:
            computation[rhs] = lhs
            generated_code[i] = f'{lhs} = {rhs}'

    return list(filter(None, '\n'.join(generated_code).split('\n')))


def code_stats(code: List[str]):
    adds = mults = subs = 0
    ptxt_mults = 0
    for line in code:
        mults += line.count('*') + line.count(">>")
        adds += line.count(",") * line.count("blend") + line.count('+')
        subs += line.count('-')
        ptxt_mults += line.count("@")

    return adds, mults, ptxt_mults


if __name__ == '__main__':
    code = """__t0 = [a:0, a:1, a:2]
__t1 = [a:0, a:1, a:2]
__v0 = __t0 ~ __t1
__s0 = __v0 >> 2
__s1 = __v0 >> 1
__t2 = [b:0, b:1, b:2]
__t3 = [b:0, b:1, b:2]
__v1 = __t2 ~ __t3
__s2 = __v1 >> 2
__s3 = __v1 >> 1
__v2 = __s0 * __s2
__v3 = __s1 * __s3
__v4 = __v2 + __v3
__v5 = __v0 * __v1
__v6 = __v5 + __v4""".split("\n")

    # print('\n'.join(push_out_rotates(code.copy())))
    print('\n'.join(remove_repeated_ops(push_out_rotates(code))))
    # seed(3)
    # e = times(times(times('d', 'b'), plus('g', times('w', 'p'))),
    #              times(times('e', 'x'), plus(plus(plus('h', 'n'), 'q'), 'o')))
    # e = fuzzer(0.9)
    # print(expr)

    # comp = Compiler({})
    # comp.compile(e)

    # e1 = times('a', plus('b', 'c'))
    # e2 = times('d', plus('e', 'f'))

    # comp = Compiler({})
    # comp.compile(e1)
    # comp.compile(e)
    # print('\n'.join(map(str, comp.code)))
    # code = vector_compile(comp)
    # print('\n'.join(code))

    # import sys
    # seed = 33
    # Expression = Union['Var', 'Op']

    # exprs = [treeGenerator(3) for i in range(1)]
    # comp = Compiler({})
    # for expr in exprs:
    #     comp.compile(expr)

    # scalar_code = list(map(str, comp.code))
    # # print('\n'.join(map(str, comp.code)))
    # vector_code = vector_compile(comp)
    # print('\n'.join(vector_code))

    # print(f'Scalar code stats: {code_stats(scalar_code)}')
    # print(f'Vector code stats: {code_stats(vector_code)}')
