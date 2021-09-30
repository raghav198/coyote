from collections import defaultdict
from time import time
from path_semiring import LangSemiring, Matrix, Path, adjacency_matrix_from_graph, is_zero
from graph import Edge, Graph, Node, connect, edges_on_path
from itertools import combinations
from typing import Callable, Dict, FrozenSet, Iterator, List, Optional, Set, Tuple, TypeVar
import z3


Relation = FrozenSet[Node]
HyperGraph = Tuple[Set[Node], List[Relation[Node]]]
Color = TypeVar('Color')


def build_hypergraph_with_path_semiring(graph: Graph[Node], stages: List[List[Node]]) -> HyperGraph[Edge]:
    node_stage: Dict[Node, int] = {}
    for i, stage in enumerate(stages):
        for node in stage:
            node_stage[node] = i

    hyperedges: Set[Relation[Edge]] = set()
    edges: Set[Edge] = set()

    # compute all cycles and paths
    adj, nodes = adjacency_matrix_from_graph(graph)
    print('Built adjacency matrix')
    powers = [adj]
    cycles: Set[Path] = set()
    while True:
        start = time()
        new_power = powers[-1] * adj
        end = time()
        print(f'Computed {len(powers)} so far ({end - start})')
        for j in range(len(nodes)):
            if len(powers) != 1 and new_power.vals[j][j] != LangSemiring.zero():
                cycles.update(new_power.vals[j][j].vals) # type: ignore
            new_power.vals[j][j] = LangSemiring.zero()

        powers.append(new_power)
        if is_zero(new_power):
            break


    total = sum(powers, Matrix(adj.mat, len(nodes)))
    for stage in stages:
        for v1, v2 in combinations(stage, 2):
            paths: Set[Path] = total.vals[nodes.index(v1)][nodes.index(v2)].vals
            hyperedges.update({frozenset(path.p) for path in paths})

    for cycle in cycles:
        print('cycle', cycle)
        hyperedges.add(frozenset(cycle.p))
        

    for v1 in graph:
        for v2 in graph[v1]:
            edges.add(Edge(v1, v2))

    return (edges, list(hyperedges))

# def build_hypergraph(graph: Graph[Node], stages: List[List[Node]], start: Node) -> HyperGraph[Edge]:
#     node_stage: Dict[Node, int] = {}
#     for i, stage in enumerate(stages):
#         for node in stage:
#             node_stage[node] = i

#     hyperedges: Set[Relation[Edge]] = set()
#     edges: Set[Edge] = set()
#     nodes: Set[Node] = set()
    
#     stack: List[Tuple[Node, Path[Node]]] = [(start, [])]
#     while len(stack) > 0:
#         # pop off the top
#         cur_node, cur_path = stack[0]
#         del stack[0]

#         nodes.add(cur_node)

#         if len(cur_path) > 0:
#             edges.add(Edge(cur_node, cur_path[-1]))

#         if cur_node in cur_path: # found a cycle
#             cycle = cur_path[cur_path.index(cur_node):] + [cur_node]
#             print(f'Cycle: {cycle}')
#             hyperedges.add(frozenset(edges_on_path(cycle)))
#             continue


#         for node in cur_path:
#             if node_stage[node] == node_stage[cur_node]:
#                 path = cur_path[cur_path.index(node):] + [cur_node]
#                 print(f'Path: {path}')
#                 hyperedges.add(frozenset(edges_on_path(path)))

        
#         new_path = cur_path + [cur_node] # to prevent aliasing
#         stack = [(adj, new_path) for adj in graph[cur_node] if len(cur_path) == 0 or adj != cur_path[-1]] + stack

#     return (edges, list(hyperedges))




def distance_computation_graph(n) -> Tuple[Graph[str], List[List[str]]]:
    stages = []
    stages.append([f'x{i + 1}' for i in range(n)])
    stages.append([f'y{i + 1}' for i in range(n)])
    stages.append([f'z{i + 1}' for i in range((n * (n + 1)) // 2)])

    graph: Graph[str] = defaultdict(list)

    cur_z = 0
    for x_index in range(n):
        for _ in range(n - x_index):
            connect(graph, f'x{x_index + 1}', f'z{cur_z + 1}')
            cur_z += 1

    cur_z = 0
    for j in range(n):
        for y_index in range(j, n):
            connect(graph, f'y{y_index + 1}', f'z{cur_z + 1}')
            cur_z += 1

    return graph, stages


def matrix_multiply_graph(n) -> Tuple[Graph[str], List[List[str]]]:
    stages = []
    stages.append([f'a{i}#{j}' for i in range(n) for j in range(n)])
    stages.append([f'b{i}#{j}' for i in range(n) for j in range(n)])
    stages.append([f'c{i}#{j}' for i in range(n) for j in range(n)])

    graph: Graph[str] = defaultdict(list)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                connect(graph, f'c{i}#{j}', f'a{i}#{k}')
                connect(graph, f'c{i}#{j}', f'b{k}#{j}')
            # connect(graph, f'c{i}#{j}', f'd')

    return graph, stages

def color_hypergraph(hypergraph: HyperGraph[Node], colors: Callable[[], Iterator[Color]]) -> Dict[Node, Color]:
    nodes, relations = hypergraph
    node_constraints: Dict[Node, List[int]] = defaultdict(list)
    for i, relation in enumerate(relations):
        for node in relation:
            node_constraints[node].append(i)

    node_coloring: Dict[Node, Color] = {} #defaultdict(lambda: next(colors()))

    def num_constraints(node: Node) -> int:
        colored_nodes = set(node_coloring.keys())
        return len(list(filter(lambda idx: (not relations[idx].issubset(colored_nodes)), node_constraints[node])))

    def next_node_to_color() -> Optional[Node]:
        colored_nodes = set(node_coloring.keys())
        uncolored_nodes = nodes - colored_nodes
        # print(f'Uncolored nodes: {uncolored_nodes}')
        if not len(uncolored_nodes): # no nodes left to color
            return None
        best = max(uncolored_nodes, key=num_constraints)
        # print(f'Returning {best}')
        return best

    def assign_color(node: Node) -> Color:
        # print(f'Trying to color {node}')
        colored_nodes = set(node_coloring.keys())
        active_constraints = [relations[idx] for idx in node_constraints[node] if len(relations[idx] - colored_nodes) == 1]
        # print(f'Active: {active_constraints}')
        disallowed_colors: Set[Color] = set()

        for constraint in active_constraints:
            # print(f'Considering {constraint - {node}}...')
            for n in constraint - {node}:
                disallowed_colors.add(node_coloring[n])

        return next(col for col in colors() if col not in disallowed_colors)

    while True:
        next_node = next_node_to_color()
        if next_node is None:
            break
        color = assign_color(next_node)
        node_coloring[next_node] = color
        print(f'Colored {next_node} as {color}')

    return node_coloring


def colors():
    i = 1
    while True:
        yield f'd{i}'
        i += 1


def integrate_colored_edges(coloring: Dict[Edge, str], graph: Graph[str], stages: List[List[str]]):
    nodes: Dict[str, z3.IntNumRef] = {}
    deltas: Dict[str, z3.IntNumRef] = {}

    node_stage: Dict[str, int] = {}
    for i, stage in enumerate(stages):
        for node in stage:
            node_stage[node] = i

    opt = z3.Solver()
    
    for node in sum(stages, []):
        nodes[node] = z3.Int(node)
        opt.add(0 <= nodes[node])
        opt.add(nodes[node] < max(map(len, stages)))

    for stage in stages:
        for x, y in combinations(stage, 2):
            opt.assert_and_track(nodes[x] != nodes[y], f'{x} != {y}')

    for v1 in graph:
        for v2 in graph[v1]:
            if node_stage[v1] < node_stage[v2]:
                color = coloring[Edge(v1, v2)]
                if color not in deltas:
                    deltas[color] = z3.Int(color)
                opt.assert_and_track(nodes[v1] == nodes[v2] + deltas[color], f'{v1} == {v2} + {color}')

    # opt.add(nodes['x1'] == 0)
    # opt.add(nodes['x2'] == 1)
    # opt.add(nodes['x3'] == 2)

    # opt.add(nodes['y1'] == 1)
    # opt.add(nodes['y2'] == 0)
    # opt.add(nodes['y3'] == 2)


    if opt.check() == z3.unsat:
        print(opt.unsat_core())
        # for constraint in opt.unsat_core():
        #     print(str(constraint))
        # unsat_core = list(map(str, opt.unsat_core()))
        raise SystemExit()
        
        

    model = opt.model()
    assignment: Dict[str, int] = {}
    for node in nodes:
        assignment[node] = model[nodes[node]].as_long()

    return assignment

if __name__ == '__main__':
    graph, stages = distance_computation_graph(3)
    # graph, stages = matrix_multiply_graph(2)
    hypergraph = build_hypergraph_with_path_semiring(graph, stages)
    # hypergraph = build_hypergraph(graph, stages, 'x1')

    # for relation in hypergraph[1]:
    #     print(relation)

    # print(hypergraph[0])

    coloring = color_hypergraph(hypergraph, colors)
    print(integrate_colored_edges(coloring, graph, stages))

    print(max(map(len, stages)))

