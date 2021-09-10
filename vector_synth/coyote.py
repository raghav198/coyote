from multiply_determinant_kernel import get_2x2_determinant
from ast_def import Compiler, fuzzer
from random import seed
from sys import argv
from vector_compiler import vector_compile

if __name__ == '__main__':

    if len(argv) != 3:
        print(f'Usage: {argv[0]} [scalar_output] [vector_output]')
        raise SystemExit()

    scalar_file = argv[1]
    vector_file = argv[2]

    # expr = get_2x2_determinant()
    # input_groups = [{
    #     'a:0,0', 'a:0,1', 'a:0,2',
    #     'a:1,0', 'a:1,1', 'a:1,2',
    #     'a:2,0', 'a:2,1', 'a:2,2'}, {
    #         'b:0,0', 'b:0,1', 'b:0,2',
    #         'b:1,0', 'b:1,1', 'b:1,2',
    #         'b:2,0', 'b:2,1', 'b:2,2'}]
    # c = Compiler({}, input_groups)

    seed(33)
    exprs = [fuzzer(0.7) for _ in range(4)]
    # exprs = [expr]

    c = Compiler({})
    tag_list = []
    for expr in exprs:
        tag_list.append(c.compile(expr))

    scalar_code_to_write = '\n'.join(map(str, c.code))
    scalar_code_to_write = ' '.join(map(str, tag_list)) + '\n' + scalar_code_to_write
    open(scalar_file, 'w').write(scalar_code_to_write)

    vector_code, width = vector_compile(c)
    open(vector_file, 'w').write(f'{width}\n' + '\n'.join(vector_code))

    print(f'Vector width = {width}')
