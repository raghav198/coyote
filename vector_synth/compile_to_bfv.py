import os
from sys import argv


def compile_scalar(lines):

    vars_used = set()

    def convert(arg):
        if arg.startswith('%'):
            return f'regs[{arg[1:]}]'

        vars_used.add(arg)
        return f'locs["{arg}"]'

    output_regs = lines[0].split(' ')
    computation_lines = []
    for line in lines[1:]:
        dest, args = line.split(' = ')
        if '+' in args:
            lhs, rhs = args.split(' + ')
            computation_lines.append(f'info.eval->add({convert(lhs)}, {convert(rhs)}, {convert(dest)});')
        elif '-' in args:
            lhs, rhs = args.split(' - ')
            computation_lines.append(f'info.eval->sub({convert(lhs)}, {convert(rhs)}, {convert(dest)});')
        elif '*' in args:
            lhs, rhs = args.split(' * ')
            computation_lines.append(f'info.eval->multiply({convert(lhs)}, {convert(rhs)}, {convert(dest)});')
            computation_lines.append(f'info.eval->relinearize_inplace({convert(dest)}, rk);')
        elif '~' in args:
            lhs, rhs = args.split(' ~ ')
            computation_lines.append(f'{convert(dest)} = {convert(lhs)};')

    computation_lines.append('std::vector<ctxt> answer;')
    for reg in output_regs:
        computation_lines.append(f'answer.push_back({convert(reg)});')
    computation_lines.append('return answer;')

    vars_used_vector = '{' + ', '.join(f'"{var}"' for var in vars_used) + '}'

    program = """
# include "../scalar.hpp"
int ScalarProgram::num_registers()
{{
    return {};
}}

std::vector<std::string> ScalarProgram::vars_used()
{{
    return {};
}}

std::vector<ctxt> ScalarProgram::computation(std::map<std::string, ctxt> locs, RuntimeContext &info)
{{
    seal::RelinKeys rk = info.keys->rk;
    ctxt regs[num_registers()];
    {}
}}
    """.format(len(lines) - 1, vars_used_vector, "\n    ".join(computation_lines))
    return program


def compile_vector(lines):
    def convert(name):
        return f'{name[2]}s[{name[3:]}]'
    mask_set = set()
    num_ts = sum(map(lambda line: line.startswith('__t'), lines))
    num_vs = sum(map(lambda line: line.startswith('__v'), lines))
    num_ss = sum(map(lambda line: line.startswith('__s'), lines))

    prep_temps = [f'std::vector<ctxt> ts({num_ts});']
    prep_masks = ['std::map<std::string, ptxt> bits;']
    compute = []

    for line in lines[1:]:
        print(line)
        dest, args = line.split(' = ')
        if args.startswith('['):
            print(line)
            input_num = int(dest[3:])
            input_liveness = '"' + ''.join([('1' if c != '0' else c) for c in args[1:-1].replace(', ', '')]) + '"'
            prep_temps.append(f'ts[{input_num}] = encrypt_input({input_liveness}, info);')
            continue
        elif '~' in args:
            lhs, rhs = args.split(' ~ ')
            compute.append(f'{convert(dest)} = {convert(lhs)}; // vector load instr')
        elif '+' in args:
            lhs, rhs = args.split(' + ')
            compute.append(f'info.eval->add({convert(lhs)}, {convert(rhs)}, {convert(dest)}); // {line}')
        elif '-' in args:
            lhs, rhs = args.split(' - ')
            compute.append(f'info.eval->sub({convert(lhs)}, {convert(rhs)}, {convert(dest)}); // {line}')
        elif '*' in args:
            lhs, rhs = args.split(' * ')
            compute.append(f'info.eval->multiply({convert(lhs)}, {convert(rhs)}, {convert(dest)}); // {line}')
            compute.append(f'info.eval->relinearize_inplace({convert(dest)}, rk);')
        elif 'blend' in args:
            compute.append('')
            compute.append(f'// {line}')
            blendees = args[6:-1].split(', ')
            need_to_mask = list(filter(lambda b: not b.startswith('__t'), blendees))
            direct_blends = list(filter(lambda b: b.startswith('__t'), blendees))
            mask_dests = [f'{dest[2:]}_{i + 1}' for i in range(len(need_to_mask))]

            compute.append(f'ctxt {", ".join(mask_dests)};')

            for maskee, mask_dest in zip(need_to_mask, mask_dests):
                val, mask = maskee.split('@')
                compute.append(f'info.eval->multiply_plain({convert(val)}, bits["{mask}"], {mask_dest});')
                mask_set.add(mask)

            summands = mask_dests + list(map(lambda b: convert(b.split('@')[0]), direct_blends))
            sum_arg = ', '.join(summands)
            if len(summands) == 2:
                compute.append(f'info.eval->add({sum_arg}, {convert(dest)});')
            else:
                compute.append(f'info.eval->add_many({{{sum_arg}}}, {convert(dest)});')
            compute.append('')

        elif '>>' in args:
            lhs, rhs = args.split(' >> ')
            compute.append(f'info.eval->rotate_rows({convert(lhs)}, -{rhs}, gk, {convert(dest)}); // {line}')
    compute.append(f'return vs[{num_vs - 1}];')

    for mask in mask_set:
        prep_masks.append(f'add_bitstring(bits, "{mask}", info);')
    prep_masks.append('return bits;')

    prep_temps.append('return ts;')

    program = """
# include "../vector.hpp"

std::map<std::string, ptxt> VectorProgram::make_bits(RuntimeContext &info)
{{
    {}
}}

std::vector<ctxt> VectorProgram::initialize_temps(RuntimeContext &info)
{{
    {}
}}

ctxt VectorProgram::computation(std::vector<ctxt> ts, std::map<std::string, ptxt> bits, RuntimeContext &info)
{{
    seal::RelinKeys rk = info.keys->rk;
    seal::GaloisKeys gk = info.keys->gk;

    ctxt vs[{}];
    ctxt ss[{}];

    {}
}}
    """.format('\n    '.join(prep_masks), '\n    '.join(prep_temps), num_vs, num_ss, '\n    '.join(compute))

    return program


def get_lines(filename):
    return list(map(str.strip, open(filename).readlines()))


if __name__ == '__main__':

    if len(argv) != 2:
        print(f'Usage: {argv[0]} [program_name]')
        raise SystemExit()

    program_name = argv[1]

    scalar_lines = get_lines(f'outputs/{program_name}/scal')
    vector_lines = get_lines(f'outputs/{program_name}/vec')

    scalar_cpp = compile_scalar(scalar_lines)
    vector_cpp = compile_vector(vector_lines)

    try:
        os.mkdir(f'bfv_backend/{program_name}')
    except FileExistsError:
        pass

    open(f'bfv_backend/{program_name}/scalar.cpp', 'w').write(scalar_cpp)
    open(f'bfv_backend/{program_name}/vector.cpp', 'w').write(vector_cpp)

    # lines = get_lines('outputs/small/vec')
    # print(compile_vector(lines))
