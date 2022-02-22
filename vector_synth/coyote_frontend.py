# from collections import namedtuple
from dataclasses import dataclass
from inspect import signature
from ast_def import Compiler, Var
from vector_compiler import vector_compile

@dataclass
class matrix:
    rows: int
    cols: int
    replicate: bool = False

@dataclass
class vector:
    size: int
    replicate: bool = False

@dataclass
class scalar:
    pass

# matrix = namedtuple('matrix', 'rows cols')
# vector = namedtuple('vector', 'size')
# scalar = namedtuple('scalar', '')

class coyote_compiler:
    def __init__(self):
        self.func_signatures = {}

    def vectorize(self):
        return vector_compile(self.compiler)

    def instantiate(self, *funcs):
        input_groups = []
        outputs = []

        if len(funcs) == 0:
            funcs = self.func_signatures
        else:
            funcs = list(filter(lambda func: func.__name__ in funcs, self.func_signatures.keys()))

        for func in funcs:
            signature = self.func_signatures[func]
            params = {}
            for _p, t in signature.items():
                p = f'{func.__name__}({_p})'
                if isinstance(t, matrix):
                    params[_p] = [[Var(f'{p}:{i},{j}') for i in range(t.rows)] for j in range(t.cols)]
                    input_groups.append({f'{p}:{i},{j}' for i in range(t.rows) for j in range(t.cols)})
                elif isinstance(t, vector):
                    params[_p] = [Var(f'{p}:{i}') for i in range(t.size)]
                    input_groups.append({f'{p}:{i}' for i in range(t.size)})
                else:
                    params[_p] = Var(p)

            out = func(**params)
            if isinstance(out, list) or isinstance(out, tuple):
                outputs += out
            else:
                outputs.append(out)
            
        self.compiler = Compiler({}, input_groups=input_groups)

        for out in outputs:
            self.compiler.compile(out)

        return list(map(str, self.compiler.code))


    def define_circuit(self, **types):
        
        def wrapper(func):
        
            name = func.__name__
            allowed_types = [matrix, vector, scalar]

            params = signature(func).parameters

            for p in types:
                if p not in params:
                    raise TypeError(f"In function '{name}': no such parameter '{p}'")
                if not any(isinstance(types[p], t) for t in allowed_types):
                    print(f"In function '{name}': '{types[p]}' is not an allowed type")



            if any(param.kind == param.VAR_KEYWORD for param in params.values()):
                raise TypeError(f"In function '{name}': keyword arguments not allowed")

            if any(param.kind == param.VAR_POSITIONAL for param in params.values()):
                raise TypeError(f"In function '{name}': positional arguments not allowed")

            for p in params:
                if p not in types:
                    types[p] = scalar()
                    print(f"In function '{name}': No type provided for {p}, assuming scalar")

            self.func_signatures[func] = types
            return func

        return wrapper


def recursive_sum(vals):
    if len(vals) == 1:
        return vals[0]
    mid = len(vals) // 2
    return recursive_sum(vals[:mid]) + recursive_sum(vals[mid:])





if __name__ == '__main__':
    coyote = coyote_compiler()

    # VEC_SIZE = 8
    # @coyote.define_circuit(a=vector(VEC_SIZE), b=vector(VEC_SIZE))
    # def dot_product(a, b):
    #     return recursive_sum([a[i] * b[i] for i in range(VEC_SIZE)])

    MAT_SIZE = 2
    @coyote.define_circuit(a=matrix(MAT_SIZE, MAT_SIZE), b=matrix(MAT_SIZE, MAT_SIZE))
    def matrix_multiply(a, b):
        output = []
        for i in range(MAT_SIZE):
            row = []
            for j in range(MAT_SIZE):
                row.append(recursive_sum([a[i][k] * b[k][j] for k in range(MAT_SIZE)]))
            output += row

        return output[0] * output[3] - output[1] * output[2]


    # IMG_SIZE = 3
    # KER_SIZE = 2
    # @coyote.define_circuit(ker=matrix(KER_SIZE, KER_SIZE), img=matrix(IMG_SIZE, IMG_SIZE))
    # def convolve(ker, img):
    #     output = []
    #     for i in range(IMG_SIZE - KER_SIZE + 1):
    #         for j in range(IMG_SIZE - KER_SIZE + 1):
    #             vals = []
    #             for k1 in range(KER_SIZE):
    #                 for k2 in range(KER_SIZE):
    #                     vals.append(img[i + k1][j + k2] * ker[k1][k2])
    #             output.append(recursive_sum(vals))
    #     return output


    scalar_code = coyote.instantiate()
    vectorized_code, width = coyote.vectorize()

    print('\n'.join(scalar_code))
    print('\n'.join(vectorized_code))
    