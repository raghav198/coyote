from collections import defaultdict
from itertools import combinations
from typing import Dict, FrozenSet, Iterator, List, Optional, Set, Tuple, TypeVar
import z3

Node = TypeVar('Node')
Color = TypeVar('Color')
Graph = Dict[Node, List[Node]]

class Edge(frozenset):
    def __new__(cls, v1, v2):
        return super().__new__(cls, {v1, v2})

    def __repr__(self):
        v1, v2 = self
        return f'{v1} -- {v2}'

def find_cycles(graph: Graph[Node], start: Node):
    cycles: Dict[FrozenSet[Node], List[Node]] = {}

    stack: List[Tuple[Node, List[Node]]] = [(start, [])]
    while len(stack) > 0:
        vertex, path = stack[0]
        del stack[0]

        # print(f'Visiting {vertex}: {path}')

        if vertex in path:
            # found a cycle
            cycle = path[path.index(vertex):]
            cycles[frozenset(cycle)] = cycle # hash this way to prevent storing duplicates that differ by a cyclic permutation
            continue
    
        new_path = path + [vertex]
        stack = [(adj, new_path) for adj in graph[vertex] if len(path) == 0 or adj != path[-1]] + stack

    return cycles

def connect(graph: Graph[Node], v1: Node, v2: Node):
    graph[v1].append(v2)
    graph[v2].append(v1)


def build_graph_for_distances(num: int) -> Graph[str]:
    graph: Graph[str] = defaultdict(list)
    cur_z = 0
    for x_index in range(num):
        for _ in range(num - x_index):
            connect(graph, f'x{x_index + 1}', f'z{cur_z + 1}')
            cur_z += 1

    cur_z = 0
    for j in range(num):
        for y_index in range(j, num):
            connect(graph, f'y{y_index + 1}', f'z{cur_z + 1}')
            cur_z += 1

    return graph


def get_edges_from_cycle(cycle: List[Node], loopback=False) -> Set[Edge]:
    edges: Set[Edge] = set()
    for v1, v2 in zip(cycle[:-1], cycle[1:]):
        edges.add(Edge(v1, v2))
    if loopback:
        edges.add(Edge(cycle[0], cycle[-1]))
    return edges

Constraint = Set[Edge]

def get_active_constraints(constraints: List[Constraint], edge_colors: Dict[Edge, Color]):
    colored_edges = set(edge_colors.keys())
    return [constraint for constraint in constraints if len(constraint - colored_edges) == 1]

def get_most_annoying_edge(constraints: List[Constraint], edge_constraints: Dict[Edge, List[int]], edge_colors: Dict[Edge, Color]) -> Optional[Edge]:
    colored_edges = set(edge_colors.keys())
    def get_num_constraints(edge: Edge) -> int:
        return len(list(filter(lambda idx: (not constraints[idx].issubset(colored_edges)), edge_constraints[edge])))

    if not len(set(edge_constraints.keys()) - colored_edges):
        return None
    return max(set(edge_constraints.keys()) - colored_edges, key=get_num_constraints)


def color_edge(edge: Edge, constraints: List[Constraint], edge_constraints: Dict[Edge, List[int]], edge_colors: Dict[Edge, Color], colors: Iterator[Color]) -> Color:
    colored_edges = set(edge_colors.keys())
    active_constraints = [constraints[idx] for idx in edge_constraints[edge] if len(constraints[idx] - colored_edges) == 1]
    disallowed_colors: Set[Color] = set()

    for constraint in active_constraints:
        for e in constraint - {edge}:
            disallowed_colors.add(edge_colors[e])

    return next(col for col in colors if col not in disallowed_colors)

def colors() -> Iterator[str]:
    i = 1
    while True:
        yield f'd{i}'
        i += 1

def one_run():
    # Node = str
    # Color = str

    graph = build_graph_for_distances(3)
    # print(graph)

    cycles = find_cycles(graph, 'x2')
    # print(cycles)

    stage1 = ['x1', 'x2', 'x3']
    stage2 = ['y1', 'y2', 'y3']
    stage3 = ['z1', 'z2', 'z3', 'z4', 'z5', 'z6']

    constraints: List[Constraint] = []

    stages = [stage1, stage2, stage3]
    node_to_stage: Dict[str, int] = {}
    for i, stage in enumerate(stages):
        for node in stage:
            node_to_stage[node] = i

        for v1, v2 in combinations(stage, 2):
            for vertices, cycle in cycles.items():
                if v1 in vertices and v2 in vertices:
                    p = cycle.index(v1)
                    q = cycle.index(v2)
                    p, q = min(p, q), max(p, q)

                    print(cycle[p:q+1], cycle[q:] + cycle[:p+1], v1, v2)

                    constraints.append(get_edges_from_cycle(cycle[p:q+1]))
                    constraints.append(get_edges_from_cycle(cycle[q:] + cycle[:p+1]))

    constraints += [get_edges_from_cycle(cycle, loopback=True) for cycle in cycles.values()]
    
    for stage in stages:
        for node in stage:
            for v1, v2 in combinations(graph[node], 2):
                if node_to_stage[v1] == node_to_stage[v2]:
                    print(f'Cone {v1} <- {node} -> {v2}')
                    constraints.append({Edge(node, v1), Edge(node, v2)})
    
    edge_constraints: Dict[Edge, List[int]] = defaultdict(list)
    for i, constraint in enumerate(constraints):
        for edge in constraint:
            edge_constraints[edge].append(i)

    

    edge_colors: Dict[Edge, str] = defaultdict(lambda: next(colors()))

    for constraint in constraints:
        print(constraint)


    while True:
        next_edge_to_color = get_most_annoying_edge(constraints, edge_constraints, edge_colors)
        if next_edge_to_color is None:
            break
        color_to_apply = color_edge(next_edge_to_color, constraints, edge_constraints, edge_colors, colors())
        edge_colors[next_edge_to_color] = color_to_apply

        print(f'Colored {next_edge_to_color} as {color_to_apply}')

    # now, all the edges are colored; time to integrate to assign lanes!
    
    nodes: Dict[str, z3.IntNumRef] = {}
    opt = z3.Solver()
    for node in sum(stages, []):
        nodes[node] = z3.Int(node)
        opt.add(0 <= nodes[node])
        opt.add(nodes[node] < max(map(len, stages)))

    deltas: Dict[str, z3.IntNumRef] = {}

    for stage in stages:
        for x, y in combinations(stage, 2):
            opt.assert_and_track(nodes[x] != nodes[y], f'{x} != {y}')

    for v1 in graph:
        for v2 in graph[v1]:
            if node_to_stage[v1] < node_to_stage[v2]:
                color = edge_colors[Edge(v1, v2)]
                if color not in deltas:
                    deltas[color] = z3.Int(color)
                opt.assert_and_track(nodes[v1] == nodes[v2] + deltas[color], f'{v1} == {v2} + {color}')

    opt.add(deltas[next(colors())] == 0)


    if opt.check() == z3.unsat:
        print(opt.unsat_core())
        return False

    model = opt.model()
    for node in nodes:
        print(f'{node}: {model[nodes[node]]}')

    return True


if __name__ == '__main__':
    one_run()
    # for i in range(1000):
    #     print(f'i = {i+1}/1000')
    #     if not one_run():
    #         break
    # else:
    #     print('SUCCESS!')

    
    

