import os
from coyote import coyote_compiler, vector, scalar, matrix, recursive_sum, Var, alternating_sum
from sys import argv

coyote = coyote_compiler()

@coyote.define_circuit(xs=vector(5), ys=vector(5))
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

@coyote.define_circuit(a=matrix(3, 3), b=matrix(3, 3))
def matmul3x3(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(3)]) for i in range(3) for j in range(3)]


@coyote.define_circuit(a=matrix(2, 2), b=matrix(2, 2))
def matmuldet(a, b):
    c = matmul2x2(a, b)
    return c[0] * c[3] - c[1] * c[2]

@coyote.define_circuit(a=matrix(2, 2), b=matrix(2, 2))
def weird_stuff(a, b):
    return conv(matmul2x2(a, b), a[0])


def cond(b, true, false):
    return b * true + (Var('1') + b) * false
    
@coyote.define_circuit(c12=scalar(), c23=scalar(), c13=scalar(), 
                       o123=scalar(), o132=scalar(), o213=scalar(), o231=scalar(), o312=scalar(), o321=scalar())
def sort_3(c12, c23, c13, o123, o132, o213, o231, o312, o321):
    return cond(c12, 
                (cond(c23, 
                    o123,
                    cond(c13, o132, o312))), 
                (cond(c13,
                    o213,
                    cond(c23, o231, o321))))



@coyote.define_circuit(a=scalar(), b=scalar(), c=scalar(), d=scalar(), x=scalar(), y=scalar(), z=scalar(), w=scalar())
def arith(a, b, c, d, x, y, z, w):
    return ((a+b) * (c+d)) * ((x+y) * (z+w))

@coyote.define_circuit(a=vector(2), x=vector(2))
def arith2(a, x):
    return ((a[0] + x[0]) * (a[0] + x[1])) * ((a[1] + x[0]) * (a[1] + x[1]))


@coyote.define_circuit(x=vector(3))
def arith3(x):
    s1 = x[0] + x[1]
    s2 = x[0] + x[2]
    s3 = x[1] + x[2]

    p1 = s1 * s2
    p2 = s2 * s3
    return p1 * p2

@coyote.define_circuit(a1=scalar(), a2=scalar(), a3=scalar(), a4=scalar(), a5=scalar(), a6=scalar(), a7=scalar(), a8=scalar())
def arith4(a1, a2, a3, a4, a5, a6, a7, a8):
    x = [a1, a2, a3, a4, a5, a6, a7, a8]
    lhs = (x[0] + x[1]) * (x[2] + x[3])
    rhs = (x[4] + x[5]) * (x[6] + x[7])
    return lhs + rhs

@coyote.define_circuit(x=vector(8))
def stuff(x):
    first_half = [x[i] for i in range(4)]
    second_half = [x[i + 4] for i in range(4)]
    a = recursive_sum(first_half)
    b = recursive_sum(second_half)
    return a * b


@coyote.define_circuit(xs=vector(3), ys=vector(3))
def distances_real(xs, ys):
    def sq(n):
        return n * n
    return [sq(xs[i] - xs[j]) + sq(ys[i] - ys[j]) for i in range(len(xs)) for j in range(len(xs)) if i != j]



def dot(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

def matvec_mul(A, b):
    result = []
    for i in range(len(A)):
        result.append(dot(A[i], b))
    return result

def convolve(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        slice = [sig[i + offset] for i in range(len(ker))]
        output.append(dot(ker, slice))
    return output


# def determinant(x):
#     return x[0] * x[3] - x[1] * x[2]

@coyote.define_circuit(vals=vector(6))
def computation(vals):
    A1 = convolve(vals[:4], vals[4:])
    A2 = convolve(vals[2:], vals[:2])
    A3 = vals[::2]

    b = [determinant(vals[:4]), determinant(vals[2:]), determinant(vals[:2] + vals[4:])]

    return matvec_mul([A1, A2, A3], b)

    
@coyote.define_circuit(A=matrix(5, 5))
def determinant(A):
    def minor(A, i):
        remove_row = A[:i] + A[i+1:]
        remove_first_col = []
        for row in remove_row:
            remove_first_col.append(row[1:])
        return remove_first_col
    sz = len(A)
    if len(A) == 1:
        return A[0][0]
    vals = []
    for i in range(sz):
        vals.append(A[i][0] * determinant(minor(A, i)))

    return alternating_sum(vals)

def usage():
    print(f'Usage: {argv[0]} [list|build] [benchmark_name?]')
    raise SystemExit()

if __name__ == '__main__':
    # argv.append('build')
    # argv.append('arith4')
    if len(argv) < 2:
        usage()

    command = argv[1]
    if command == 'list':
        print('List of available benchmarks:')
        for func in coyote.func_signatures:
            print(f'* {func.__name__}')
    elif command == 'build':
        if len(argv) < 3:
            print(f'Error: command "build" but no benchmark was specified (try `{argv[0]} list` to list available benchmarks)')
            usage()
        benchmark_names = argv[2:]
        for benchmark_name in benchmark_names:
            print(f'Building {benchmark_name}...')
            scalar_code = coyote.instantiate(benchmark_name)
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
            

    
