from sys import stdout
from ast_def import Expression, Var
from typing import Dict, List, Tuple
from progressbar import ProgressBar

MATCH_MUL = 1
MATCH_ADD = 1

class SimilarityCache:
    def __init__(self):
        self.cache: Dict[Tuple[int, int], MatchResult] = {}

    def __call__(self, f):
        def cached_sim(a: Expression, b: Expression):
            if isinstance(a, Var) or isinstance(b, Var):
                return f(a, b)
            if (a.tag, b.tag) not in self.cache:
                self.cache[a.tag, b.tag] = self.cache[b.tag, a.tag] = f(a, b)

            return self.cache[a.tag, b.tag]

        return cached_sim


class MatchResult:
    def __init__(self, matches: List[Tuple[int, int]] = [], scores: List[int] = []):
        assert len(matches) == len(scores)

        self.matches = matches
        self.scores = scores

    def __add__(self, other):
        assert isinstance(other, MatchResult)
        return MatchResult(self.matches + other.matches, self.scores + other.scores)

    def __gt__(self, other):
        assert isinstance(other, MatchResult)
        return sum(self.scores) > sum(other.scores)


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
    match = MatchResult([(a.tag, b.tag)], scores=[(MATCH_MUL if a.op == '*' else MATCH_ADD)]) if a.op == b.op else MatchResult()
    options.append(similarity(a.lhs, b.lhs) + similarity(a.rhs, b.rhs) + match)
    options.append(similarity(a.lhs, b.rhs) + similarity(a.rhs, b.lhs) + match)

    return max(options)