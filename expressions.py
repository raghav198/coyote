from __future__ import annotations
from collections import defaultdict
from typing import Dict, List
from bicont import *


def state_vecs(tree: Type2Phi) -> Dict[str, List[Expr]]:
    def outputs(node: CopseIR):
        assert not isinstance(node, Type2Phi)
        if isinstance(node, Type1Phi):
            return outputs(node.true) + outputs(node.false)
        elif isinstance(node, Output):
            if node.secret:
                return [node.args]
            else:
                return []

    states = defaultdict(list)
    for out in outputs(tree.first):
        for var, val in zip(tree.vars, out):
            states[var].append(val)
    return dict(states)


def copse_compile(tree: CopseIR) -> str:
    if isinstance(tree, Type1Phi):
        return f"Branch {{threshold = Threshold {{feat = \"{tree.lhs}\", val = \"{tree.rhs}\"}}, left = {copse_compile(tree.false)}, right = {copse_compile(tree.true)}}}"
    elif isinstance(tree, Type2Phi):
        first = copse_compile(tree.first)
        second = copse_compile(tree.second)
        glue = f"secret_reveal({state_vecs(tree)})"
        return f"{first}\n{glue}\n{second}"
    elif isinstance(tree, Output):
        return f"Label (L {tree.args})"
    raise NotImplementedError


print(copse_compile(compile(gcd_program)))

# print(program_nested)
# compiled = compile(program_nested)
# assert isinstance(compiled, Type2Phi)
# print(state_vecs(compiled))
# print(compiled.first)
