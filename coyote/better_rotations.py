from functools import reduce
from .codegen import VecBlendInstr, VecConstInstr, VecInstr, VecLoadInstr, VecOpInstr, VecRotInstr


def better_rotations(code: list[VecInstr], vector_width: int):

    # accumulated: dict[str, int] = {}
    
    def apply(shift: int, track: dict[str, int]):
        return {var: rot + shift for var, rot in track.items()}
    
    def combine(track1: dict[str, int], track2: dict[str, int]):
        return {var: max(track1.get(var, 0), track2.get(var, 0), key=abs) for var in track1.keys() | track2.keys()}
    
    def limiter(track: dict[str, int]):
        return max(track.values(), key=abs)
    
    accumulated: dict[str, dict[str, int]] = {} # destination -> (input -> rotation)
    
    for line in code:
        # print(f'Rotations so far: {accumulated}')
        match line:
            case VecRotInstr(dest, operand, shift):
                positive, negative = (shift, shift - vector_width) if shift > 0 else (shift + vector_width, shift)
                if abs(limiter(apply(positive, accumulated[operand]))) < abs(limiter(apply(negative, accumulated[operand]))):
                # if accumulated[operand] + negative < 0 or abs(accumulated[operand] + positive) < abs(accumulated[operand] + negative):
                    line.shift = positive
                else:
                    line.shift = negative
                accumulated[dest] = apply(line.shift, accumulated[operand])
            case VecOpInstr(dest, _, lhs, rhs):
                accumulated[dest] = combine(accumulated[lhs], accumulated[rhs])
            case VecLoadInstr(dest, src):
                accumulated[dest] = accumulated[src]
            case VecConstInstr(dest, _):
                accumulated[dest] = {dest: 0}
            case VecBlendInstr(dest, vals, _):
                accumulated[dest] = reduce(combine, (accumulated[val] for val in vals), {})
                # accumulated[dest] = max(accumulated[val] for val in vals)
    return code, max(map(limiter, accumulated.values())), min(map(limiter, accumulated.values())), accumulated
            