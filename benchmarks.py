import os
from coyote.coyote import *
from sys import argv

coyote = coyote_compiler()

def cond(b, true, false):
    return b * true + (Var('1') + b) * false

# Decision Tree Benchmark
@coyote.define_circuit(c12=scalar(), c23=scalar(), c13=scalar(), o123=scalar(), o132=scalar(), o213=scalar(), o231=scalar(), o312=scalar(), o321=scalar())
def decision_tree(c12, c23, c13, o123, o132, o213, o231, o312, o321):
    return cond(c12, 
                (cond(c23, 
                    o123,
                    cond(c13, o132, o312))), 
                (cond(c13,
                    o213,
                    cond(c23, o231, o321))))

# Fully Replicated Benchmarks
@coyote.define_circuit(xs=vector(5, replicate=True), ys=vector(5, replicate=True))
def distances_5x5_fully(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(xs=vector(4, replicate=True), ys=vector(4, replicate=True))
def distances_4x4_fully(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(xs=vector(3, replicate=True), ys=vector(3, replicate=True))
def distances_3x3_fully(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(a=matrix(2, 2, replicate=True), b=matrix(2, 2, replicate=True))
def matmul_2x2_fully(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(len(a))]) for i in range(len(a)) for j in range(len(a))]

@coyote.define_circuit(a=matrix(3, 3, replicate=True), b=matrix(3, 3, replicate=True))
def matmul_3x3_fully(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(len(a))]) for i in range(len(a)) for j in range(len(a))]

@coyote.define_circuit(sig=vector(4, replicate=True), ker=vector(2, replicate=True))
def conv_4x2_fully(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
    return output

@coyote.define_circuit(sig=vector(5, replicate=True), ker=vector(3, replicate=True))
def conv_5x3_fully(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
    return output

@coyote.define_circuit(v1=vector(3, replicate=True), v2=vector(3, replicate=True))
def dot_product_3x3_fully(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(v1=vector(6, replicate=True), v2=vector(6, replicate=True))
def dot_product_6x6_fully(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(v1=vector(10, replicate=True), v2=vector(10, replicate=True))
def dot_product_10x10_fully(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(cs=vector(3, replicate=True), os=vector(6, replicate=True))
def decision_tree_packed_fully(cs, os):
    return cond(cs[0], 
                (cond(cs[1], 
                    os[0],
                    cond(cs[2], os[1], os[4]))), 
                (cond(cs[2],
                    os[2],
                    cond(cs[1], os[3], os[5]))))

# Partially Replicated Benchmarks
@coyote.define_circuit(xs=vector(5, replicate=True), ys=vector(5))
def distances_5x5_partially(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(xs=vector(4, replicate=True), ys=vector(4))
def distances_4x4_partially(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(xs=vector(3, replicate=True), ys=vector(3))
def distances_3x3_partially(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(a=matrix(2, 2, replicate=True), b=matrix(2, 2))
def matmul_2x2_partially(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(len(a))]) for i in range(len(a)) for j in range(len(a))]

@coyote.define_circuit(a=matrix(3, 3, replicate=True), b=matrix(3, 3))
def matmul_3x3_partially(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(len(a))]) for i in range(len(a)) for j in range(len(a))]

@coyote.define_circuit(sig=vector(4), ker=vector(2, replicate=True))
def conv_4x2_partially(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
    return output

@coyote.define_circuit(sig=vector(5), ker=vector(3, replicate=True))
def conv_5x3_partially(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
    return output

@coyote.define_circuit(v1=vector(3, replicate=True), v2=vector(3))
def dot_product_3x3_partially(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(v1=vector(6, replicate=True), v2=vector(6))
def dot_product_6x6_partially(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(v1=vector(10, replicate=True), v2=vector(10))
def dot_product_10x10_partially(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(cs=vector(3, replicate=True), os=vector(6))
def decision_tree_packed_partially(cs, os):
    return cond(cs[0], 
                (cond(cs[1], 
                    os[0],
                    cond(cs[2], os[1], os[4]))), 
                (cond(cs[2],
                    os[2],
                    cond(cs[1], os[3], os[5]))))

# Unreplicated Benchmarks
@coyote.define_circuit(xs=vector(5), ys=vector(5))
def distances_5x5_un(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(xs=vector(4), ys=vector(4))
def distances_4x4_un(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(xs=vector(3), ys=vector(3))
def distances_3x3_un(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(a=matrix(2, 2), b=matrix(2, 2))
def matmul_2x2_un(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(len(a))]) for i in range(len(a)) for j in range(len(a))]

@coyote.define_circuit(a=matrix(3, 3), b=matrix(3, 3))
def matmul_3x3_un(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(len(a))]) for i in range(len(a)) for j in range(len(a))]

@coyote.define_circuit(sig=vector(4), ker=vector(2))
def conv_4x2_un(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
    return output

@coyote.define_circuit(sig=vector(5), ker=vector(3))
def conv_5x3_un(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
    return output

@coyote.define_circuit(v1=vector(3), v2=vector(3))
def dot_product_3x3_un(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(v1=vector(6), v2=vector(6))
def dot_product_6x6_un(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(v1=vector(10), v2=vector(10))
def dot_product_10x10_un(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(cs=vector(3), os=vector(6))
def decision_tree_packed_un(cs, os):
    return cond(cs[0], 
                (cond(cs[1], 
                    os[0],
                    cond(cs[2], os[1], os[4]))), 
                (cond(cs[2],
                    os[2],
                    cond(cs[1], os[3], os[5]))))

@coyote.define_circuit(xs=vector(3), ys=vector(3))
def distances(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]


@coyote.define_circuit(sig=vector(4), ker=vector(2))
def conv(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
    return output


@coyote.define_circuit(a=matrix(2, 2), b=matrix(2, 2))
def matmul2x2(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(2)]) for i in range(2) for j in range(2)]


@coyote.define_circuit(a=matrix(2, 2), b=matrix(2, 2))
def weird_stuff(a, b):
    return conv(matmul2x2(a, b), a[0])


def cond(b, true, false):
    return b * true + (Var('1') + b) * false
    
@coyote.define_circuit(c12=scalar(), c23=scalar(), c13=scalar(), o123=scalar(), o132=scalar(), o213=scalar(), o231=scalar(), o312=scalar(), o321=scalar())
def sort_3(c12, c23, c13, o123, o132, o213, o231, o312, o321):
    return cond(c12, 
                (cond(c23, 
                    o123,
                    cond(c13, o132, o312))), 
                (cond(c13,
                    o213,
                    cond(c23, o231, o321))))


def usage():
    print(f'Usage: {argv[0]} [list|build] [benchmark_name?]')
    raise SystemExit()

if __name__ == '__main__':
    if len(argv) < 2:
        usage()

    command = argv[1]
    if command == 'list':
        print('List of available benchmarks:')
        for func in coyote.func_signatures:
            print(f'* {func.__name__}')
    elif command == 'build':
        if len(argv) != 3:
            print(f'Error: command "build" but no benchmark was specified (try `{argv[0]} list` to list available benchmarks)')
            usage()
        benchmark_name = argv[2]
        scalar_code = coyote.instantiate(argv[2])
        vector_code = coyote.vectorize()

        try:
            os.mkdir('outputs')
        except FileExistsError:
            pass
        
        try:
            os.mkdir(f'outputs/{benchmark_name}')
        except FileExistsError:
            pass

        open(f'outputs/{benchmark_name}/scal', 'w').write('\n'.join(scalar_code))
        open(f'outputs/{benchmark_name}/vec', 'w').write('\n'.join(vector_code))
        print(f'Successfully compiled benchmark {benchmark_name}; outputs placed in "outputs/{benchmark_name}"!')
        

    