from coyote.coyote import *

coyote = coyote_compiler()

@coyote.define_circuit(a=matrix(2, 2, replicate=True), b=matrix(2, 2, replicate=True))
def matmul(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(len(a))]) for i in range(len(a)) for j in range(len(a))]

@coyote.define_circuit(a=matrix(2, 2), b=matrix(2, 2))
def matmuldet(a, b):
    prod = matmul(a, b)
    return prod[0] * prod[3] - prod[1] * prod[2]

@coyote.define_circuit(sig=vector(4), ker=vector(2))
def conv(sig, ker):
    output = []
    for offset in range(len(sig) - len(ker) + 1):
        output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
    return output


@coyote.define_circuit(xs=vector(5), ys=vector(5))
def distances(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]


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


@coyote.define_circuit(cs=vector(3), os=vector(6))
def sort_3_packed(cs, os):
    return cond(cs[0], 
                (cond(cs[1], 
                    os[0],
                    cond(cs[2], os[1], os[4]))), 
                (cond(cs[2],
                    os[2],
                    cond(cs[1], os[3], os[5]))))


@coyote.define_circuit(v1=vector(4), v2=vector(4))
def dot_product(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])


scalar_code = coyote.instantiate('conv', 'dot_product')
vector_code = coyote.vectorize()

print('\n'.join(scalar_code))
print('=' * 20)
print('\n'.join(vector_code))
