from collections import defaultdict
from ast_def import Compiler, plus, times
from eva import EvaProgram, Input, Output
from eva.ckks import CKKSCompiler
from eva.seal import generate_keys
from io import StringIO
from vector_compiler import vector_compile


def better_sum(args):
    return sum(args[1:], args[0])


def get_bitlist(bitstring):
    bits = []
    power = 1
    for char in bitstring[::-1]:
        if char == '1':
            bits.append(f'bit{power}')
        power *= 2
    return bits


def make_generator_evaluator(vector_code, width):
    def input_generator(**inputs):
        if inputs == {}:
            inputs = defaultdict(lambda: 0)
        generated_inputs = {}
        for line in vector_code:
            dest, command = line.split(' = ')
            if not command.startswith('['):
                continue
            vals = command[1:-1].split(', ')
            value = []
            for val in vals:
                if val == '0' or val == '1':
                    value.append(int(val))
                else:
                    value.append(inputs[val])
            generated_inputs[dest] = value
        for i in range(width):
            generated_inputs[f'bit{2**i}'] = [int(i == j) for j in range(width - 1, -1, -1)]
        return generated_inputs

    def evaluator(**inputs):
        locs = dict(**inputs)

        for line in vector_code:
            dest, command = line.split(' = ')
            if command.startswith('['):
                continue
            if '+' in command:
                lhs, rhs = command.split(' + ')
                locs[dest] = locs[lhs] + locs[rhs]
            elif '*' in command:
                lhs, rhs = command.split(' * ')
                locs[dest] = locs[lhs] * locs[rhs]
            elif 'blend' in command:
                args = command[6:-1].split(', ')
                pieces = []
                for arg in args:
                    var, mask = arg.split('@')
                    pieces.append(locs[var] * better_sum([locs[bit] for bit in get_bitlist(mask)]))
                locs[dest] = better_sum(pieces)
            elif '>>' in command:
                lhs, rhs = command.split(' >> ')
                locs[dest] = locs[lhs] >> int(rhs)
            else:
                raise Exception(f'What does "{line}" mean??')
            last_dest = dest
        return locs[last_dest]
    return input_generator, evaluator


def build_eva_program(vector_code, width, iscale=100, oscale=100):
    gen, func = make_generator_evaluator(vector_code, width)
    program = EvaProgram('prog', vec_size=width)
    with program:
        inputs = {key: Input(key) for key in gen()}
        Output('answer', func(**inputs))

    program.set_input_scales(iscale)
    program.set_output_ranges(oscale)

    return program, gen


def compile_eva_prog(program):
    compiler = CKKSCompiler()
    compiled, params, sig = compiler.compile(program)
    public, secret = generate_keys(params)

    return compiled, public, secret, sig


if __name__ == '__main__':
    # input expressions
    e1 = plus(times('a', 'b'), 'c')
    e2 = times(times('a', 'c'), plus('b', 'd'))
    e3 = plus('a', times('b', plus('c', times('d', 'e'))))

    # compile to scalar code (serialize trees)
    c = Compiler({})
    c.compile(e1)
    c.compile(e2)
    c.compile(e3)

    # vectorize
    vector_code, width = vector_compile(c, log=StringIO())
    vector_code.append('ans = blend(__v1@0010, __v3@1100)')  # hack needed for now to put outputs on the same vector

    # compile to EVA backend
    program, get_inputs = build_eva_program(vector_code, width, iscale=100, oscale=100)
    compiled, public, secret, sig = compile_eva_prog(program)

    # execute compiled EVA program
    inputs = get_inputs(a=1, b=2, c=3, d=4, e=5)
    enc_in = public.encrypt(inputs, sig)
    enc_out = public.execute(compiled, enc_in)
    outputs = secret.decrypt(enc_out, sig)

    print(outputs)
