from time import time
from covectorizability_graph import build_graph, BreaksetCalculator
from ast_def import *
from typing import Dict
from vectorize import build_vector_program
import z3

seed(4)


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


if __name__ == '__main__':
    # Generate a random expression for testing
    expr = fuzzer(0.9)
    print(expr)

    # Compile to a scalar program
    tag_lookup: Dict[int, Op] = {}
    comp = Compiler(tag_lookup)
    comp.compile(expr)
    code = comp.code

    start = time()

    print('\n'.join(map(str, code)))

    vector_cost_estimate = 0
    final_vector_code = []

    bkset_calc = BreaksetCalculator(*build_graph(expr, tag_lookup))

    quotients = []
    # Get an optimal set of breakpoints for this stage
    unused_outputs = set()
    interstage_dicts = []
    intrastage_dicts = []
    final_stage = False
    while not final_stage:
        bkset, _ = bkset_calc.solve()  # get_breakset(expr, tag_lookup)
        if len(bkset) == 0:
            final_stage = True
            bkset = [expr.tag]
        bkset_calc.disallow(bkset)
        for b in bkset:
            bkset_calc.disallow(list(filter(lambda t: isinstance(t, int), tag_lookup[b].subtags)))
        # expr = quotient_relative_expression(expr, bkset)

        # Scalar program for this stage
        stage_code = sum([lookup_code(code, bk, quotients) for bk in bkset], [])

        quotients += bkset
        intermediates = [instr.dest.val for instr in stage_code]

        print('\n'.join(map(str, stage_code)))
        vectorized_code = build_vector_program(stage_code, len(bkset))
        unused_outputs |= set(bkset)
        # print('vector code: ', vectorized_code)
        # print('stage inputs: ', stage_inputs)

        vector_cost_estimate += len(vectorized_code) + len(bkset)
        final_vector_code += vectorized_code

        print('\n'.join(map(str, vectorized_code)))
        # print([instr.dest for instr in stage_code])
        # print(lanes)

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
        # print(f'=== insert code to shuffle {bkset} ===')

    # now, generate scalar code for whatever remains
    # stage_code = lookup_code(code, expr.tag, quotients)
    # stage_dicts.append(
    #     {expr.tag: set(filter(lambda l: l in unused_outputs, tag_lookup[expr.tag].subtags))})

    # vectorized_code = build_vector_program(stage_code, 1)
    # # print(lanes)
    # vector_cost_estimate += len(vectorized_code)
    print('=' * 30)
    print('FINAL VECTORIZED CODE:')
    print('\n'.join(map(str, final_vector_code)))

    end = time()

    print('=' * 30)
    print('STAGE DICTIONARIES:')
    print(interstage_dicts)
    print(intrastage_dicts)

    # print(f'Synthesized vector program in {int(1000 * (end - start))} ms')
    # print(f'Reduced {len(code)} scalar instructions to approx {vector_cost_estimate}')



    opt = z3.Solver()
    _lane =  z3.IntVector('lane', len(code))
    _arr =  z3.IntVector('arr', len(code))
    for l in range(0,len(code)):
        opt.add(_lane[l] >= 0)

    #Set up the || chain
    for stage_dict in interstage_dicts:
        for key in stage_dict.keys():
            opt.add(z3.And([_lane[key] != _lane[key1] for key1 in stage_dict.keys() if key!=key1] ))
    for stage_dict in interstage_dicts[1:]:
        for key,val in stage_dict.items():
	        opt.add(z3.Or([_lane[key] == _lane[i] for i in val]))
  
    opt.check()
    print(opt.model())
    #print("jsccn")
    '''#if more than one value is produced in same vector
    length = 1
    for k in range(0,len(code)):
    #Set up the || chain
        for stage_dict in stage_dicts:
	        for key,val in stage_dict.items():
		        for i in range(0,length):
			        opt.add(z3.Or([_lane[key] == _lane[j] + arr[i] for j in val]))
        if(opt.check() == z3.sat):
            print(opt.model())
            break
        else:
            print("jsccn")
            length += 1'''
    

