from typing import List, Tuple
import z3
from sys import stderr


class BreaksetCalculator:
    def __init__(self, connections: List[Tuple[int]], weights: List[List[Tuple[int]]], timeout=10):
        self.connections = connections
        self.weights = weights
        self.num_nodes = max(sum(connections, ())) + 1
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

    def update_connections(self):
        for con in range(len(self.connections)):
            a, b = self.connections[con]
            self.clique_weights[con] = z3.If(z3.And(
                self.in_clique[a] == 1, self.in_clique[b] == 1), len(self.weights[con]), 0)

    def disallow(self, tags):
        weights = []
        for weight in self.weights:
            weights.append(list(filter(lambda p: p[0] not in tags and p[1] not in tags, weight)))

        self.weights = weights

        for tag in tags:
            try:
                self.opt.add(self.in_clique[tag] == 0)
            except IndexError:
                print(
                    f'Warning: attempting to disallow a nonexistent tag {tag} (if this is the last stage, its probably fine)')

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
                    z3.Sum(self.clique_weights))
                print(f'Current best: {value}', file=stderr)
                self.opt.add(
                    z3.Sum(self.clique_weights) > value)
            else:
                self.opt.pop()
                print(f'Breakset has {len(clique)} nodes', file=stderr)
                return clique, value


def solve_MaxClique(connections, weights):
    solver = BreaksetCalculator(connections, weights)
    return solver.solve()


if __name__ == '__main__':
    connections = [(0, 1), (0, 2), (1, 2),
                   (0, 3), (3, 4), (2, 4)]

    weights = [1, 3, 2, 14, 3, 3]

    print(solve_MaxClique(connections, weights))
