from ast_def import Expression, Var
from typing import List, Tuple

class SimilarityCache:
    def __init__(self):
        self.cache = {}

    def __call__(self, f):
        def cached_sim(a: Expression, b: Expression):
            if isinstance(a, Var) or isinstance(b, Var):
                return f(a, b)
            if (a.tag, b.tag) not in self.cache:
                self.cache[a.tag, b.tag] = f(a, b)
            return self.cache[a.tag, b.tag]

        return cached_sim


class MatchResult:
    def __init__(self, matches: List[Tuple[int, int]] = []):
        self.matches = matches

    def __add__(self, other):
        assert isinstance(other, MatchResult)
        return MatchResult(self.matches + other.matches)

    def __gt__(self, other):
        assert isinstance(other, MatchResult)
        return len(self.matches) > len(other.matches)


cache = SimilarityCache()

@cache
def similarity(a: Expression, b: Expression) -> MatchResult:
    if isinstance(a, Var) or isinstance(b, Var):
        return MatchResult()

    options = []
    
    # if A and B don't line up
    options.append(similarity(a, b.lhs))
    options.append(similarity(a, b.rhs))
    options.append(similarity(a.lhs, b))
    options.append(similarity(a.rhs, b))

    # if A and B line up
    match = MatchResult([(a.tag, b.tag)]) if a.op == b.op else MatchResult()
    options.append(similarity(a.lhs, b.lhs) + similarity(a.rhs, b.rhs) + match)
    options.append(similarity(a.lhs, b.rhs) + similarity(a.rhs, b.lhs) + match)

    return max(options)