from itertools import cycle

from coyote import *
from coyote.vectorize_circuit import vectorize
import pickle 
import time
import multiprocessing

start_time = time.time()

coyote = coyote_compiler()

def dot(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

def add(v1, v2):
    return [a + b for a, b in zip(v1, v2)]

@coyote.define_circuit(A=matrix(3, 3), B=matrix(3, 3))
def block3x3(A, B):
    return [dot(A[i], B[j]) for i in range(2) for j in range(2)]

@coyote.define_circuit(a=matrix(3, 3), b=matrix(3, 3))
def matmul3x3(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(3)]) for i in range(3) for j in range(3)]

@coyote.define_circuit(A=scalar(), B=scalar(), C=scalar(), D=scalar(), E=scalar(), F=scalar(), G=scalar(), H=scalar())
def block4x4(A,B,C,D,E,F,G,H):
    return [A*E + B*G, A*F + B*H, C*E + D*G, C*F+D*H]

# @coyote.define_circuit(v1=scalar(), v2=scalar(), v3=scalar(), v4=scalar(), v5=scalar(), v6=scalar())
# def dot9(v1, v2, v3, v4, v5, v6, v7, v8):
#     return [v1 * v5 + v2 * v6 , v3 * v7 + v4 * v8]

@coyote.define_circuit(v1=vector(9), v2=vector(9))
def dot6(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(v1=scalar(), v2=scalar(), v3=scalar(),v4=scalar(), v5=scalar(), v6=scalar())
def dot9(v1, v2, v3, v4, v5, v6):
    return v1*v2 + v3*v4+ v5*v6

@coyote.define_circuit(v1=vector(3), v2=vector(3))
def dot3(v1, v2):
    return recursive_sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(A=scalar(), B=scalar(), C=scalar(), D=scalar(), E=scalar(), F=scalar(), G=scalar(), H=scalar())
def block4x4(A,B,C,D,E,F,G,H):
    return [A*E + B*G, A*F + B*H, C*E + D*G, C*F+D*H]

@coyote.define_circuit(A=scalar(), B=scalar())
def block2(A,B):
    return [A*B+ B*A]

@coyote.define_circuit(xs=vector(9), ys=vector(9))
def dot6_for(xs, ys):
    sum = dot3(xs[0:2], ys[0:2])
    for i in range(1,3):
        sum = sum + dot3(xs[i*3:3*i+2], ys[3*i:3*i+2], sum)
    return sum 

@coyote.define_circuit(sig_size=scalar(), ker_size=scalar())
def get_conv(sig_size, ker_size):   
    @coyote.define_circuit(sig=vector(sig_size), ker = vector(ker_size))
    def convolve(sig, ker):
        output = []
        for offset in range(len(sig) - len(ker) + 1):
            output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
        return output
    return convolve


# @coyote.define_circuit(conv1=scalar(), conv2=scalar())
# def conv_block4x4(conv1, conv2):
#     conv = [conv1, conv2]
#     return conv

# @coyote.define_circuit(A=matrix(2, 2), B=matrix(2, 2))
# def loop(A,B):

#     result = [[sum(A[i][k] * B[k][j] for k in range(2)) for j in range(2)] for i in range(2)]
#     result_flat = [item for sublist in result for item in sublist]

#     return result_flat

# @coyote.define_circuit(v1=vector(5), v2=vector(5))
# def loop(v1, v2):
#     out = [0, 0, 0, 0, 0]
#     for i in range(5):
#         out[i] = v1[i] + v2[i]
#     return out

# @coyote.define_circuit(v1=vector(1), v2=vector(1))
# def loop1(v1, v2):
#     out = [0]
#     for i in range(1):
#         out[i] = v1[i] + v2[i]
#     return out

# @coyote.define_circuit(loop1=scalar(), loop2=scalar(), loop3=scalar())
# def loop_tiling(loop1, loop2, loop3):
#   return [loop1 + loop2 +loop3]

# @coyote.define_circuit(v1=vector(3), v2=vector(3))
# def loop2(v1, v2):
#     out = [0, 0, 0]
#     for i in range(0):
#         out[i] = v1[i] + v2[i]
#     return out
# @coyote.define_circuit(v1=vector(3))
# def dot3_operation(v1):
#     return v1[0] * v1[1] * v1[1]

# @coyote.define_circuit(v1=vector(3), v2=vector(3))
# def one_dot3(v1, v2):

#     dot_result_1 = dot3_operation(v1) 
#     dot_result_2 = dot3_operation(v2)  
#     combined_result = dot_result_1 + dot_result_2
    
#     return combined_result

# @coyote.define_circuit(v1=vector(8), v2=vector(4))
# def loop1(v1, v2):
#     output = [] 
#     for i in range(4):
#         sum = 0 
#         for j in range(5):
#             sum = recursive_sum([v1[i + j] * v2[j] for j in range(len(v2))])
#         output.append(sum)
@coyote.define_circuit(xs=vector(5), ys=vector(5))
def distances(xs, ys):
    return [(x - y) * (x - y) for x in xs for y in ys]

@coyote.define_circuit(v1=vector(8), v2=vector(4))
def loop1(v1, v2):
    output = []
    for i in range(3):
            output.append(recursive_sum([v1[i + k] * v2[k] for k in range(4)]))
    return output

@coyote.define_circuit(v1=vector(8), v2=vector(4))
def loop2(v1, v2):
    output = []
    for i in range(3,5):
            output.append(recursive_sum([v1[i + k] * v2[k] for k in range(4)]))
    return output


@coyote.define_circuit(a=matrix(4, 4), b=matrix(4, 4))
def loop1_matrix(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(2)]) for i in range(2) for j in range(2)]

@coyote.define_circuit(a=matrix(4, 4), b=matrix(4, 4))
def loop2_matrix(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(2, 4)]) for i in range(2, 4) for j in range(2, 4)]


@coyote.define_circuit(a=matrix(9, 9), b=matrix(9, 9))
def loop1_matrix_9(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(3)]) for i in range(3) for j in range(3)]

@coyote.define_circuit(a=matrix(9, 9), b=matrix(9, 9))
def loop2_matrix_9(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(3,6)]) for i in range(3,6) for j in range(3,6)]

@coyote.define_circuit(a=matrix(9, 9), b=matrix(9, 9))
def loop3_matrix_9(a, b):
    return [recursive_sum([a[i][k] * b[k][j] for k in range(6,9)]) for i in range(6,9) for j in range(6, 9)]


@coyote.define_circuit(v1=vector(10), v2=vector(5))
def loop1_conv102(v1, v2):
    output = []
    for i in range(2):
            output.append(recursive_sum([v1[i + k] * v2[k] for k in range(5)]))
    return output

@coyote.define_circuit(v1=vector(10), v2=vector(5))
def loop2_conv102(v1, v2):
    output = []
    for i in range(6):
            output.append(recursive_sum([v1[i + k] * v2[k] for k in range(5)]))
    return output

@coyote.define_circuit(v1=vector(10), v2=vector(5))
def loop3_conv102(v1, v2):
    output = []
    for i in range(4,6):
            output.append(recursive_sum([v1[i + k] * v2[k] for k in range(5)]))
    return output

@coyote.define_circuit(v1=vector(8), v2=vector(4))
def conv8by4(v1, v2):
    output = []
    for i in range(5):
            output.append(recursive_sum([v1[i + k] * v2[k] for k in range(4)]))
    return output

@coyote.define_circuit(v1=vector(10), v2=vector(5))
def conv10by2(v1, v2):
    output = []
    for i in range(6):
            output.append(recursive_sum([v1[i + k] * v2[k] for k in range(5)]))
    return output


@coyote.define_circuit(xs=vector(10), ys=vector(10))
def distances_1_1(xs, ys):
    return [(x - y) * (x - y) for x in xs[:5] for y in ys[:5]]

@coyote.define_circuit(xs=vector(10), ys=vector(10))
def distances_2_2(xs, ys):
    return [(x - y) * (x - y) for x in xs[5:10] for y in ys[5:10]]

def process_sequence(instantiate_label, file_name):
    coyote.instantiate(instantiate_label)
    # code = vectorize(coyote.compiler)
    code_object = vectorize(coyote.compiler)
    file_out = [coyote.compiler.code, code_object]

    with open(file_name, "wb") as file:
        # Serialize the object and write it to the file
        pickle.dump(file_out, file)

    # Capture the start time

def main():
    start_time = time.time()
    
    # Process arguments (label and filename)
    processes_info = [
        ('loop1_conv102', 'loop1_conv102.pkl'),
        ('loop2_conv102', 'loop2_conv102.pkl'),
        ('loop3_conv102', 'loop3_conv102.pkl'),
    ]
    
    # Create a list to keep track of processes
    processes = []
    
    # Initialize and start processes
    for instantiate_label, file_name in processes_info:
        p = multiprocessing.Process(target=process_sequence, args=(instantiate_label, file_name))
        p.start()
        processes.append(p)
    
    # Wait for all processes to complete
    for p in processes:
        p.join()
    
    # Calculate elapsed time
    end_time = time.time()
    elapsed_time = end_time - start_time
    print('Convolutoin 10 by 2 With Titling')
    print(f"Elapsed time: {elapsed_time} seconds")

if __name__ == '__main__':
    main()