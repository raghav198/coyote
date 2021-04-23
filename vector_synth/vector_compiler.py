from time import time
from covectorizability_graph import build_graph, BreaksetCalculator
from ast_def import *
from typing import Dict
from vectorize import build_vector_program


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

    bkset_calc = BreaksetCalculator(*build_graph(expr, tag_lookup))

    quotients = []
    # Get an optimal set of breakpoints for this stage
    while True:
        bkset, _ = bkset_calc.solve()  # get_breakset(expr, tag_lookup)
        if len(bkset) == 0:
            break
        bkset_calc.disallow(bkset)
        for b in bkset:
            bkset_calc.disallow(list(filter(lambda t: isinstance(t, int), tag_lookup[b].subtags)))
        # expr = quotient_relative_expression(expr, bkset)

        # Scalar program for this stage
        stage_code = sum([lookup_code(code, bk, quotients) for bk in bkset], [])
        quotients += bkset

        # print('\n'.join(map(str, stage_code)))
        vectorized_code = build_vector_program(stage_code, len(bkset))

        vector_cost_estimate += len(vectorized_code) + len(bkset)

        print('\n'.join(map(str, vectorized_code)))
        print(f'=== insert code to shuffle {bkset} ===')

    # now, generate scalar code for whatever remains
    stage_code = lookup_code(code, expr.tag, quotients)
    vectorized_code = build_vector_program(stage_code, 1)
    vector_cost_estimate += len(vectorized_code)
    print('\n'.join(map(str, vectorized_code)))

    end = time()

    print(f'Synthesized vector program in {int(1000 * (end - start))} ms')
    print(f'Reduced {len(code)} scalar instructions to approx {vector_cost_estimate}')


"""
1. For each vector instruction, the list of outputs (unused until a future stage)
2. For each stage, all the inputs that correspond to a particular one of its outputs
"""
