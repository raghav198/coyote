from compile_convolution import get_matmul
from vector_compiler import Compiler, vector_compile

if __name__ == '__main__':
    comp = Compiler({})
    for entry in get_matmul('a', 'b', 2, 3, 2):
        comp.compile(entry)
    vector_code = vector_compile(comp)
    print('\n'.join(vector_code))
