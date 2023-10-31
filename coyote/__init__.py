from dataclasses import dataclass
from inspect import signature
from sys import stderr
from warnings import warn
from .coyote_ast import CompilerV2, Var
from .vectorize_circuit import vectorize

@dataclass
class matrix:
    rows: int
    cols: int
    replicate: bool = False

@dataclass
class vector:
    size: int
    replicate: bool = False
    pack: bool = False

@dataclass
class scalar:
    pass

class copy_vector:
    def __init__(self, size, name, var_conv='{name}:{i}'):
        self.size = size
        self.name = name
        self.var_conv = var_conv

    def __getitem__(self, i):
        if i >= self.size:
            raise IndexError('list index out of range')
        return Var(self.var_conv.format(name=self.name, i=i))

    def __len__(self):
        return self.size
class copy_matrix:
    def __init__(self, rows, cols, name, var_conv='{name}:{i},{j}'):
        self.name = name
        self.rows = rows
        self.cols = cols
        self.var_conv = var_conv

    def __getitem__(self, i):
        if i >= self.rows:
            raise IndexError('list index out of range')
        return copy_vector(self.cols, f'{self.name}:{i}', var_conv=f'{self.name}:{i};{{i}}')

    def __len__(self):
        return self.rows

    
class coyote_compiler:
    def __init__(self):
        self.func_signatures = {}
        self.outputs = []

    def vectorize(self, lanes_out=[]):
        return vectorize(self.compiler)


    def instantiate(self, *funcs, _input_groups=None, _force_lanes=None):
        self.outputs = []
        input_groups, force_lanes, outputs = self.get_outputs(funcs)
            
        self.compiler = CompilerV2(input_groups, force_lanes=force_lanes)

        for out in outputs:
            self.outputs.append(self.compiler.compile(out).val)

        return [' '.join(f'%{reg}' for reg in self.outputs)] + list(map(str, self.compiler.code))


    def get_outputs(self, funcs):
        input_groups = []
        force_lanes = {}
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
                    if t.replicate:
                        params[_p] = copy_matrix(t.rows, t.cols, p)
                    else:
                        params[_p] = [[Var(f'{p}:{i};{j}') for i in range(t.rows)] for j in range(t.cols)]
                    input_groups.append({f'{p}:{i};{j}' for i in range(t.rows) for j in range(t.cols)})
                elif isinstance(t, vector):
                    
                    if t.replicate and t.pack:
                        raise TypeError('`replicate` and `pack` options not allowed together!')
                    
                    if t.replicate:
                        params[_p] = copy_vector(t.size, p)
                    else:
                        params[_p] = [Var(f'{p}:{i}') for i in range(t.size)]
                    input_groups.append({f'{p}:{i}' for i in range(t.size)})
                    
                    if t.pack:
                        force_lanes.update({f'{p}:{i}': i for i in range(t.size)})
                else:
                    params[_p] = Var(p)

            out = func(**params)
            if isinstance(out, list) or isinstance(out, tuple):
                outputs += out
            else:
                outputs.append(out)
        return input_groups, force_lanes, outputs

    def define_circuit(self, **types):
        
        def wrapper(func):
        
            name = func.__name__
            allowed_types = [matrix, vector, scalar]

            params = signature(func).parameters

            for p in types:
                if p not in params:
                    raise TypeError(f"In function '{name}': no such parameter '{p}'")
                if not any(isinstance(types[p], t) for t in allowed_types):
                    raise TypeError(f"In function '{name}': '{types[p]}' is not an allowed type")



            if any(param.kind == param.VAR_KEYWORD for param in params.values()):
                raise TypeError(f"In function '{name}': keyword arguments not allowed")

            if any(param.kind == param.VAR_POSITIONAL for param in params.values()):
                raise TypeError(f"In function '{name}': positional arguments not allowed")

            for p in params:
                if p not in types:
                    types[p] = scalar()
                    warn(f"In function '{name}': No type provided for {p}, assuming scalar")

            self.func_signatures[func] = types
            return func

        return wrapper

coyote = coyote_compiler()

def recursive_sum(vals):
    if len(vals) == 1:
        return vals[0]
    mid = len(vals) // 2
    return recursive_sum(vals[:mid]) + recursive_sum(vals[mid:])


def alternating_sum(vals):
    if len(vals) == 1:
        return vals[0]
    mid = len(vals) // 2
    if mid % 2:
        return alternating_sum(vals[:mid]) - alternating_sum(vals[mid:])
    return alternating_sum(vals[:mid]) + alternating_sum(vals[mid:])