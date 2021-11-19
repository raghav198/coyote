from collections import defaultdict
from email.policy import default
import enum
from inspect import BoundArguments
from math import sqrt
from time import time

from numpy import matrix
from pyparsing import col
from path_semiring import LangSemiring, Matrix, Path, adjacency_matrix_from_graph, is_zero
from graph import Edge, Graph, Node, connect, edges_on_path
from itertools import combinations
from typing import Callable, Counter, Dict, FrozenSet, Iterator, List, Optional, Set, Tuple, TypeVar
import z3
from progressbar import ProgressBar


Relation = FrozenSet[Node]
HyperGraph = Tuple[Set[Node], List[Relation[Node]]]
Color = TypeVar('Color')


def build_hypergraph_with_path_semiring(graph: Graph[Node], stages: List[List[Node]], timeout=1000) -> HyperGraph[Edge]:
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
    start = time()
    while True:
        power_start = time()
        new_power = powers[-1] * adj
        power_end = time()
        print(f'Computed {len(powers)} so far ({power_end - power_start})')
        if 1000 * (power_end - start) > timeout - (power_end - power_start):
            print(f'Timeout...')
            break
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
            if v1 not in nodes or v2 not in nodes:
                continue
            paths: Set[Path] = total.vals[nodes.index(v1)][nodes.index(v2)].vals
            hyperedges.update({frozenset(path.p) for path in paths})

    for cycle in cycles:
        hyperedges.add(frozenset(cycle.p))
        

    for v1 in graph:
        for v2 in graph[v1]:
            edges.add(Edge(v1, v2))

    print(f'Adding {len(hyperedges)} relations')
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
    stages.append([f'z{i + 1}' for i in range((n * n))])

    graph: Graph[str] = defaultdict(list)

    cur_z = 0
    for x_index in range(n):
        for _ in range(n):
            connect(graph, f'x{x_index + 1}', f'z{cur_z + 1}')
            cur_z += 1

    cur_z = 0
    for j in range(n):
        for y_index in range(n):
            connect(graph, f'y{y_index + 1}', f'z{cur_z + 1}')
            cur_z += 1

    return graph, stages


def shuffled_distance_computation_graph(n, swap=False) -> Tuple[Graph[str], List[List[str]]]:
    stages = []
    stages.append(['x1', 'z2', 'y3', 'x4'])
    stages.append(['y1', 'x2', 'z3', 'z4'])
    stages.append(['z1', 'y2', 'x3', 'y4', 'z5', 'y6', 'x7', 'x8', 'x9', 'z10', 'z11', 'z12', 'y13', 'y14', 'x15', 'z16'])

    graph: Graph[str] = defaultdict(list)
    
    
    if swap:
        z_index = 0
        for _ in range(n):
            for yi in range(n):
                connect(graph, stages[1][yi], stages[2][z_index])
                z_index += 1

        z_index = 0
        for xi in range(n):
            for _ in range(n):
                connect(graph, stages[0][xi], stages[2][z_index])
                z_index += 1
    else:
        z_index = 0
        for xi in range(n):
            for _ in range(n):
                connect(graph, stages[0][xi], stages[2][z_index])
                z_index += 1

        z_index = 0
        for _ in range(n):
            for yi in range(n):
                connect(graph, stages[1][yi], stages[2][z_index])
                z_index += 1

    return graph, stages


def matrix_multiply_graph(n) -> Tuple[Graph[str], List[List[str]]]:
    stages = []
    stages.append([f'a{i}#{j}' for i in range(n) for j in range(n)])
    stages.append([f'b{i}#{j}' for i in range(n) for j in range(n)])
    stages.append([f'c{i}#{j}' for i in range(n) for j in range(n)])
    stages.append(['d'])

    graph: Graph[str] = defaultdict(list)
    for i in range(n):
        for j in range(n):
            for k in range(n):
                connect(graph, f'c{i}#{j}', f'a{i}#{k}')
                connect(graph, f'c{i}#{j}', f'b{k}#{j}')
            connect(graph, f'c{i}#{j}', f'd')

    return graph, stages

def color_hypergraph(hypergraph: HyperGraph[Node], colors: Callable[[], Iterator[Color]]) -> Dict[Node, Color]:
    bar = ProgressBar(maxval=len(hypergraph[0]))
    nodes, relations = hypergraph
    node_constraints: Dict[Node, List[int]] = defaultdict(list)
    for i, relation in enumerate(relations):
        for node in relation:
            node_constraints[node].append(i)


    node_coloring: Dict[Node, Color] = {} #defaultdict(lambda: next(colors()))

    def num_constraints(node: Node) -> int:
        colored_nodes = set(node_coloring.keys())
        # open_constraints = filter(lambda idx: (not relations[idx].issubset(colored_nodes)), node_constraints[node])
        # return sum((1.0 / len(relations[idx]) for idx in open_constraints)) # type: ignore
        return len(list(filter(lambda idx: (not relations[idx].issubset(colored_nodes)), node_constraints[node])))

    def next_node_to_color() -> Optional[Node]:
        colored_nodes = set(node_coloring.keys())
        uncolored_nodes = nodes - colored_nodes
        # print(f'Uncolored nodes: {uncolored_nodes}')
        if not len(uncolored_nodes): # no nodes left to color
            return None
        # sorted_uncolored_nodes = sorted(uncolored_nodes, key=repr)
        best = min(uncolored_nodes, key=lambda n: (num_constraints(n), repr(n)))
        # print(num_constraints(best))
        # print(f'Returning {best}')
        return best

    def assign_color(node: Node) -> Color:
        # print(f'Trying to color {node}')
        colored_nodes = set(node_coloring.keys())
        # all_constraints = [relations[idx] for idx in node_constraints[node]]
        disallowed_colors: Set[Color] = set()
        # if any(len(constraint - colored_nodes) == 1 for constraint in all_constraints):
        #     for constraint in all_constraints:
        #         # print(f'Considering {constraint - {node}}...')
        #         for n in constraint.intersection(colored_nodes):
        #             disallowed_colors.add(node_coloring[n])
        active_constraints = [relations[idx] for idx in node_constraints[node] if len(relations[idx] - colored_nodes) == 1]
        colors_seen_so_far: Set[Color] = set()
        for constraint in active_constraints:
                # print(f'Considering {constraint - {node}}...')
                # colors_in_this_constraint = set(node_coloring[n] for n in constraint - {node})
                # disallowed_colors.update(colors_in_this_constraint.intersection(colors_seen_so_far))
                # colors_seen_so_far.update(colors_in_this_constraint)
                for n in constraint - {node}:
                    
                    disallowed_colors.add(node_coloring[n])
        # print(f'Active: {active_constraints}')
        # print(disallowed_colors)
        

        return next(col for col in colors() if col not in disallowed_colors)

    colored = 0
    bar.start()
    while True:
        next_node = next_node_to_color()
        # print(next_node)
        # raise SystemExit()
        if next_node is None:
            break
        color = assign_color(next_node)
        node_coloring[next_node] = color
        bar.update(colored)
        colored += 1
        # input(f'Colored {next_node} as {color}')
    bar.finish()
    return node_coloring


def colors():
    i = 1
    while True:
        yield f'd{i}'
        i += 1



def find_all_paths(graph: Graph[Node], start: Node, end: Node):
    queue = [[start]]
    paths = []
    while len(queue) > 0:
        dequeue = queue[0]
        del queue[0]
        # print(f'Looking at {dequeue}')
        if dequeue[-1] == end:
            paths.append(dequeue)
            # print(f'Adding {dequeue}')
            continue

        for next_vertex in graph[dequeue[-1]]:
            if next_vertex not in dequeue:
                queue.append(dequeue + [next_vertex])
    return paths

         


def cegis_edges(unsat_core: List[str]):
    constraint_subgraph: Graph[str] = defaultdict(list)
    endpoints = []
    for line in unsat_core:
        if '!=' in line:
            start, end = line.split(' != ')
            endpoints.append((start, end))
        elif '==' in line:
            v1, v2 = line[:line.index(' +')].split(' == ')
            connect(constraint_subgraph, v1, v2)

    return constraint_subgraph

    def relation_from_path(path: List[Node]) -> Relation[Edge]:
        relation = []
        for v1, v2 in zip(path[:-1], path[1:]):
            relation.append(Edge(v1, v2))
        return frozenset(relation)


    relations: List[Relation[Edge]] = []
    for start, end in endpoints:
        paths = find_all_paths(constraint_subgraph, start, end)

        relations += [relation_from_path(path) for path in paths]

    return relations

            
def quotient_by_zero_color(coloring: Dict[Edge, Color], graph: Graph[Node], zero_color: Color):
    print(f'Setting {zero_color} to zero')
    equivalence_classes: Dict[Node, str] = {}
    next_q = 0
    for v1 in graph:
        for v2 in graph[v1]:
            if coloring[Edge(v1, v2)] == zero_color:
                if v1 in equivalence_classes:
                    equivalence_classes[v2] = equivalence_classes[v1]
                elif v2 in equivalence_classes:
                    equivalence_classes[v1] = equivalence_classes[v2]
                else:
                    equivalence_classes[v1] = f'__quotient_{next_q}'
                    equivalence_classes[v2] = f'__quotient_{next_q}'
                    next_q += 1

    return equivalence_classes


def integrate_colored_edges(coloring: Dict[Edge, Color], graph: Graph[Node], stages: List[List[Node]], bound_lanes=None, ignore=[]):
    if bound_lanes is None:
        bound_lanes = max(map(len, stages))


    print(f'Bounding by {bound_lanes}')

    nodes: Dict[Node, z3.IntNumRef] = {}
    deltas: Dict[Color, z3.IntNumRef] = {}

    node_stage: Dict[Node, int] = {}
    for i, stage in enumerate(stages):
        for node in stage:
            node_stage[node] = i

    opt = z3.Solver()
    opt.set('timeout', 20000)
    
    for node in sum(stages, []):
        nodes[node] = z3.Int(node)
        opt.add(0 <= nodes[node])
        if bound_lanes:
            opt.assert_and_track(nodes[node] < bound_lanes, f'lane_bound_{node}')

    for stage in stages:
        for x, y in combinations(stage, 2):
            opt.assert_and_track(nodes[x] != nodes[y], f'{x} != {y}')

    for v1 in graph:
        for v2 in graph[v1]:
            if node_stage[v1] < node_stage[v2]:
                color = coloring[Edge(v1, v2)]
                if color not in deltas:
                    deltas[color] = z3.Int(color)
                # if color_multiplicities[color] == 1:
                #     continue
                constraint_name = f'{v1} == {v2} + {color}'
                if constraint_name not in ignore:
                    opt.assert_and_track(nodes[v1] == nodes[v2] + deltas[color], f'{v1} == {v2} + {color}')
    
    # if force_zero is not None:
    #     opt.add(deltas[force_zero] == 0)

    # opt.add(nodes['x1'] == 0)
    # opt.add(nodes['x2'] == 1)
    # opt.add(nodes['x3'] == 2)

    # opt.add(nodes['y1'] == 1)
    # opt.add(nodes['y2'] == 0)
    # opt.add(nodes['y3'] == 2)

    new_bound = max(int(sqrt(sqrt(2)) * bound_lanes), bound_lanes + 1)

    print(f'Formulated with {len(opt.assertions())} constraints and {len(nodes), len(deltas)} variables')
    start = time()
    result = opt.check()
    if result == z3.unsat:
        unsat_core = list(map(str, opt.unsat_core()))
        print(unsat_core)

        if any(core.startswith('lane_bound') for core in unsat_core):
            print(f'Rebounding at {int(sqrt(sqrt(2)) * bound_lanes)}')
            return integrate_colored_edges(coloring, graph, stages, bound_lanes=new_bound)

        # return cegis_edges(unsat_core)
        return integrate_colored_edges(coloring, graph, stages, bound_lanes=bound_lanes, ignore=ignore + unsat_core)
        # for constraint in opt.unsat_core():
        #     print(str(constraint))
        # unsat_core = list(map(str, opt.unsat_core()))
        # raise SystemExit()

    elif result == z3.unknown and opt.reason_unknown() == 'canceled':
        print('Adding more lanes and trying again')
        return integrate_colored_edges(coloring, graph, stages, bound_lanes=new_bound)
        
    end = time()
    # print(f'Solving took {end - start} time')
    # raise SystemExit()

    model = opt.model()
    assignment: Dict[Node, int] = {}
    for node in nodes:
        assignment[node] = model[nodes[node]].as_long()

    return assignment


def split_stage_graph_3():
    stage1 = ['x1', 'x2', 'x3']
    stage2 = ['y1', 'y2', 'y3']
    stage3 = ['z1', 'z5', 'z3']
    stage4 = ['z4', 'z2', 'z6']
    stage5 = ['z7', 'z8', 'z9']

    graph: Graph[str] = defaultdict(list)
    n = 3
    cur_z = 0
    for x_index in range(n):
        for _ in range(n):
            connect(graph, f'x{x_index + 1}', f'z{cur_z + 1}')
            cur_z += 1

    cur_z = 0
    for j in range(n):
        for y_index in range(n):
            connect(graph, f'y{y_index + 1}', f'z{cur_z + 1}')
            cur_z += 1

    return graph, [stage1, stage2, stage3, stage4, stage5]


def place_lanes_hypergraph_method(dependencies: List[Dict[int, Set[int]]], max_warp: int):
    graph, stages, renum_to_orig = build_dependency_graph(dependencies)

    
    # for stage1, stage2 in zip(stages[:-1], stages[1:]):
    #     num_edges = sum(len(list(filter(lambda v2: v2 in stage2, graph[v1]))) for v1 in stage1)
    #     print(len(stage1), len(stage2), num_edges)
    # input()
    

    edges, hyperedges = build_hypergraph_with_path_semiring(graph, stages, timeout=5000)
    while True:
        coloring = color_hypergraph((edges, hyperedges), colors)


        avg_color_density = []
        for i in range(len(stages)):
            first_half = sum(stages[:i], [])
            second_half = sum(stages[i:], [])

            colors_used = set()
            num_edges = 0
            for v1 in first_half:
                cross_edges = list(filter(lambda v2: v2 in second_half, graph[v1]))
                num_edges += len(cross_edges)
                if len(cross_edges):
                    colors_used.update({coloring[Edge(v1, v2)] for v2 in cross_edges})

            if num_edges > 0:
                avg_color_density.append(num_edges / len(colors_used))

        print(avg_color_density)

                
            


            # num_edges = sum(len(list(filter(lambda v2: v2 in second_half, graph[v1]))) for v1 in first_half)
            # print(sum(map(len, stages[:i])), sum(map(len, stages[i:])), num_edges)

        # print(Counter(coloring.values()))

        # print(quotient_by_zero_color(coloring, graph, Counter(coloring.values()).most_common()[0][0]))
        # raise SystemExit()

        # color_mode = Counter(coloring.values()).most_common()[0][0]
        result = integrate_colored_edges(coloring, graph, stages)
        if type(result) is defaultdict:
            print('Unsat!')
            _, new_relations = build_hypergraph_with_path_semiring(result, stages)
            hyperedges += new_relations
            continue
        break

    return {renum_to_orig[k]: v for k, v in result.items()}

def build_dependency_graph(dependencies):
    graph: Graph[str] = defaultdict(list)
    stages: List[List] = []

    orig_to_renum: Dict[int, str] = {}
    renum_to_orig: Dict[str, int] = {}

    for i, stage in enumerate(dependencies):
        stage_keys = sorted(stage.keys())
        for j, key in enumerate(stage_keys):
            orig_to_renum[key] = f'{i}_{j}'
            renum_to_orig[f'{i}_{j}'] = key
        stages.append([orig_to_renum[stage_key] for stage_key in stage_keys])


    for stage in dependencies:
        for consumer in stage:
            for producer in stage[consumer]:
                connect(graph, orig_to_renum[consumer], orig_to_renum[producer])

    for k in graph:
        graph[k].sort()

    return graph, stages, renum_to_orig



if __name__ == '__main__':
    # graph, stages = split_stage_graph_3()
    # graph, stages = shuffled_distance_computation_graph(4, swap=True)
    # graph, stages = distance_computation_graph(4)
    graph, stages = matrix_multiply_graph(4)
    for key in graph:
        graph[key].sort()


    # graph, stages = matrix_multiply_graph(4)
    edges, hyperedges = build_hypergraph_with_path_semiring(graph, stages, timeout=5000)

    while True:
        coloring = color_hypergraph((edges.copy(), hyperedges.copy()), colors)
        # for key in sorted(coloring.keys()):
        #     print(f'{key}: {coloring[key]}')
        result = integrate_colored_edges(coloring, graph, stages)
        if type(result) is defaultdict:
            print('Unsat!')
            _, new_relations = build_hypergraph_with_path_semiring(result, stages)
            print(f'Disjoint: {len(set(new_relations).intersection(set(hyperedges)))}')
            hyperedges += new_relations
            continue
        break

    # print(result)
    for stage in stages:
        print([result[stage[i]] for i in range(len(stage))])
    # print(max(map(len, stages)))

