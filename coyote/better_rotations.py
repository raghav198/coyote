from .codegen import VecBlendInstr, VecConstInstr, VecInstr, VecLoadInstr, VecOpInstr, VecRotInstr


def better_rotations(code: list[VecInstr], vector_width: int):

    accumulated: dict[str, int] = {}
    for line in code:
        # print(f'Rotations so far: {accumulated}')
        match line:
            case VecRotInstr(dest, operand, shift):
                positive, negative = (shift, shift - vector_width) if shift > 0 else (shift + vector_width, shift)
                if abs(accumulated[operand] + positive) < abs(accumulated[operand] + negative):
                    line.shift = positive
                else:
                    line.shift = negative
                accumulated[dest] = accumulated[operand] + line.shift
            case VecOpInstr(dest, _, lhs, rhs):
                accumulated[dest] = max(accumulated[lhs], accumulated[rhs])
            case VecLoadInstr(dest, src):
                accumulated[dest] = accumulated[src]
            case VecConstInstr(dest, _):
                accumulated[dest] = 0
            case VecBlendInstr(dest, vals, _):
                accumulated[dest] = max(accumulated[val] for val in vals)
    return code, max(accumulated.values()), min(accumulated.values())
            