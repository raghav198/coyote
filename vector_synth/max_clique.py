from typing import List, Tuple
import z3
from sys import stderr
import numpy as np


class BreaksetCalculator:
    def __init__(self, num_nodes, connections: List[Tuple[int]], matches: List[List[Tuple[int]]], match_scores: List[List[int]], rotate_penalty=1, timeout=10, log=stderr):

        self.rotate_penalty = rotate_penalty
        self.log = log

        self.connections = connections
        self.matches = []

        for match in matches:
            if not len(match):
                self.matches.append((np.array([]), np.array([])))
                continue

            left, right = zip(*match)

            self.matches.append((np.array(left), np.array(right)))

        self.weights = matches

        self.match_scores = list(map(np.array, match_scores))
        self.num_nodes = num_nodes

        self.opt = z3.Solver()

        self.opt.set('timeout', timeout * 1000)

        self.in_clique = z3.IntVector(
            'in_clique', self.num_nodes)

        for i in range(self.num_nodes):
            self.opt.add(
                z3.Or(self.in_clique[i] == 0, self.in_clique[i] == 1))
            for j in range(i + 1, self.num_nodes):
                if (i, j) not in connections:
                    self.opt.add(
                        z3.Not(z3.And(self.in_clique[i] == 1, self.in_clique[j] == 1)))

        self.clique_weights = z3.IntVector(
            'clique_weights', len(connections))

        self.update_connections()

    def get_weight(self, con):
        # return len(self.weights[con])
        return int(self.match_scores[con].sum()) - self.rotate_penalty

    def update_connections(self):
        for con in range(len(self.connections)):
            a, b = self.connections[con]
            self.clique_weights[con] = z3.If(z3.And(
                self.in_clique[a] == 1, self.in_clique[b] == 1), self.get_weight(con), 0)

        # no empty cliques allowed!
        self.opt.add(z3.Sum(self.in_clique) > 0)

    def disallow(self, tags):
        # weights = []
        # for weight in self.weights:
        #     weights.append(list(filter(lambda p: p[0] not in tags and p[1] not in tags, weight)))

        for (left_match, right_match), scores in zip(self.matches, self.match_scores):
            exclude = np.logical_or(
                np.isin(left_match, tags), np.isin(right_match, tags))
            scores[exclude] = 0

        # self.weights = weights

        for tag in tags:
            try:
                self.opt.add(self.in_clique[tag] == 0)
            except IndexError:
                print(
                    f'Warning: attempting to disallow a nonexistent tag {tag} (if this is the last stage, its probably fine)', file=self.log)

        self.update_connections()

    def solve(self) -> Tuple[List[int], int]:
        # save state before
        self.opt.push()

        clique, value = [], 0
        while True:
            result = self.opt.check()
            if result == z3.sat:
                clique: List[int] = []
                model = self.opt.model()
                for node in range(self.num_nodes):
                    if model.eval(self.in_clique[node] == 1):
                        clique.append(node)
                value = model.eval(
                    z3.Sum(self.clique_weights)) if len(self.clique_weights) else 0
                print(f'Current best: {value}', file=self.log)
                self.opt.add(
                    z3.Sum(self.clique_weights) > value)
            else:
                self.opt.pop()
                print(f'Breakset has {len(clique)} nodes', file=self.log)
                return clique, value


def solve_MaxClique(connections, weights):
    solver = BreaksetCalculator(connections, weights)
    return solver.solve()


if __name__ == '__main__':
    connections = [(0, 1), (0, 2), (1, 2),
                   (0, 3), (3, 4), (2, 4)]

    weights = [1, 3, 2, 14, 3, 3]

    print(solve_MaxClique(connections, weights))
