from compile_decision_forest import get_exprs, Compiler
from ast_def import Expression, Var
from vector_compiler import fuzzer

def find_mult_chains(tree: Expression, acc):
    
    if isinstance(tree, Var):
        return
    
    find_mult_chains(tree.rhs, acc)
    find_mult_chains(tree.lhs, acc)

    if tree.op != '*':
        return

    print(f'Visiting {tree.tag}')

    if tree.lhs.tag in acc:
        chain_so_far = acc[tree.lhs.tag]
        chain_so_far.append(tree.tag)
        acc[tree.tag] = chain_so_far

    if tree.rhs.tag in acc:
        chain_so_far = acc[tree.rhs.tag]
        chain_so_far.append(tree.tag)
        acc[tree.tag] = chain_so_far

    acc[tree.tag] = [tree.tag]

if __name__ == '__main__':
    # exprs = get_exprs(open('../../copse/Baseline/benchmarks/depth4.tree').readlines())
    exprs = [fuzzer(0.9)]
    for expr in exprs:
        comp = Compiler({})
        comp.compile(expr)
        print(comp.code)
        chains = {}
        find_mult_chains(expr, chains)
        print('\n'.join(map(str, comp.code)))
        for chain_start in chains:
            print(chains[chain_start])