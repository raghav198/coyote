from ast_def import plus, times
from typing import List
from vector_compiler import Compiler, vector_compile

def get_exprs(lines: List[str]):
    exprs = []
    nodes = {}
    for line in lines:
        line = line.strip()
        if line.startswith('feats') or line.startswith('lbls'):
            continue
        if line.startswith('root'):
            exprs.append(nodes[line[5:]])
            nodes = {}
            continue
        
        node, lb, *args = line.split(' ')
        if lb == 'L':
            nodes[node] = args[0]
        else:
            nodes[node] = plus(times(node, nodes[args[2]]), times(plus('1', node), nodes[args[3]]))

    return exprs


if __name__ == '__main__':
    exprs = get_exprs(open('../../copse/Baseline/benchmarks/depth4.tree').readlines())
    comp = Compiler({})
    for expr in exprs:
        print(f'Adding {expr}')
        comp.compile(expr)


    print('\n'.join(map(str, comp.code)))
    code = vector_compile(comp)
    print('\n'.join(code))