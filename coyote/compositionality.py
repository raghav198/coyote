from coyote import *

coyote = coyote_compiler()

def dot(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(A=matrix(3, 3), b=vector(3))
def matvec_mul(A, b):
    result = []
    for i in range(len(A)):
        result.append(dot(A[i], b))
    return result

@coyote.define_circuit(signal=vector(4), kernel=vector(2))
def convolve(signal, kernel):
    output = []
    for offset in range(len(signal) - len(kernel) + 1):
        output.append(dot(kernel, signal[offset:offset+len(kernel)]))
    return output


@coyote.define_circuit(A=matrix(3, 3), sig=vector(4), ker=vector(2))
def compose(A, sig, ker):
    b = convolve(sig, ker)
    return matvec_mul(A, b)


wires = [('convolve', 'matvec_mul', 1)]

from time import time

start = time()

k1_groups, _, k1_circuits = coyote.get_outputs(['convolve'])
k1_lanes: list[int] = []
coyote.compiler = CompilerV2(k1_groups)
k1_outputs = []
for c in k1_circuits:
    k1_outputs.append(coyote.compiler.compile(c).val)

k1_code = coyote.vectorize(k1_lanes)
k1_output_lanes = [k1_lanes[out] for out in k1_outputs]

k2_groups, _, k2_circuits = coyote.get_outputs(['matvec_mul'])
k2_lanes: list[int] = []
k2_force_lanes = {v: l for v, l in zip(sorted(k2_groups[1]), k1_output_lanes)}

coyote.compiler = CompilerV2(k2_groups, force_lanes=k2_force_lanes)
k2_outputs = []
for c in k2_circuits:
    k2_outputs.append(coyote.compiler.compile(c).val)

k2_code = coyote.vectorize(k2_lanes)
k2_output_lanes = [k2_lanes[out] for out in k2_outputs]

broken_code = k1_code + k2_code

t1 = time() - start

coyote.instantiate('compose')
combined_code = coyote.vectorize([])

t2 = time() - t1 + start

print(f'=== SEPARATE KERNELS === ({t1})')
print('\n'.join(broken_code))
print(f'=== FUSED KERNELS === ({t2})')
print('\n'.join(combined_code))
print('=== END ===')


# # print(coyote.func_signatures)
# k1_outputs = coyote.instantiate('matvec_mul')[0].split()
# k1_lanes: list[int] = []

# coyote.vectorize(k1_lanes)
# print(k1_outputs)
# print(k1_lanes)

# input_groups, force_lanes, circuits = coyote.get_outputs(['convolve'])


# k2_outputs = coyote.instantiate('convolve')[0].split()

# # print(k1_outputs, k2_outputs)