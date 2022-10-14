from sys import stderr
from typing import Dict, List, Tuple
from .coyote_ast import *
from .synthesize_schedule import VecInstr
import networkx as nx # type: ignore


def build_vector_program(program: List[Instr],
                         lanes: List[int],
                         schedule: List[int], log=stderr) -> List[VecInstr]:
    print('Building stage:', file=log)
    print('\n'.join(map(str, program)), file=log)
    # print(lanes, schedule)
    vectorized_code = []
    warp = max(lanes) + 1

    # schedule  :: inst -> slot, inv_schedule :: slot -> [inst]
    inv_schedule = [[i for i in range(len(schedule)) if schedule[i] == slot]
                    for slot in set(schedule)]

    # print(inv_schedule)
    for instrs in inv_schedule:
        dest = [-1 for _ in range(warp)]
        lhs = [Atom(BLANK_SYMBOL) for _ in range(warp)]
        rhs = [Atom(BLANK_SYMBOL) for _ in range(warp)]

        for i in instrs:
            reg = program[i].dest.val
            assert isinstance(reg, int)
            lane_num: int = lanes[reg]
            dest[lane_num] = reg
            lhs[lane_num] = program[i].lhs
            rhs[lane_num] = program[i].rhs

        vectorized_code.append(VecInstr(dest, lhs, rhs, program[instrs[0]].op))

    # print('Stage:')
    # print('\n'.join(map(str, vectorized_code)))
    return vectorized_code


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


def codegen(vector_program: List[VecInstr], graph: nx.DiGraph, lanes: List[int], schedule: List[int], warp_size: int):
    shift_amounts_needed: Dict[int, Dict[int, int]] = defaultdict(lambda: defaultdict(lambda: 0))
    print('Raw program: ')
    print('\n'.join(map(str, vector_program)))
    print(f'Warp size: {warp_size}')

    for instr in vector_program:
        for c, p in zip(instr.dest * 2, instr.left + instr.right):
            if not (isinstance(p.val, int) and isinstance(c.val, int)):
                continue
            shift_amount = (lanes[c.val] - lanes[p.val]) % warp_size
            if shift_amount == 0:
                continue
            shift_amounts_needed[p.val][c.val] = shift_amount

    print(shift_amounts_needed)


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
            constants: List[str | int] = [0] * len(operands)

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

    return generated_code
    return remove_repeated_ops(generated_code)