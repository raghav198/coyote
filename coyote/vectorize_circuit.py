from collections import defaultdict
from functools import reduce
from math import exp
from random import randint, random, seed, choice
from .codegen import build_vector_program, codegen
from .disjoint_set import DisjointSet
from typing import Counter, List, Set, Dict, Tuple, Generator
from .coyote_ast import CompilerV2, Instr
import networkx as nx
from .synthesize_schedule import VecInstr, synthesize_schedule

seed(1)

MUL_PER_ROTATE = 1
ADD_PER_ROTATE = 0.1

COSTS_PER_ROTATE = defaultdict(int, {'+': ADD_PER_ROTATE, '*': MUL_PER_ROTATE})

def instr_sequence_to_nx_graph(instrs: List[Instr]) -> nx.DiGraph:
    graph = nx.DiGraph()
    graph.graph['ops'] = {}
    for instr in instrs:
        graph.graph['ops'][instr.dest.val] = instr.op
        if instr.op == '~':
            continue
        graph.add_edge((instr.lhs.val,), (instr.dest.val,))
        graph.add_edge((instr.rhs.val,), (instr.dest.val,))
        
    return graph


def grade_nx_graph(graph: nx.DiGraph, groups: List[Set[int]]):
    for node in graph:
        if 'epoch' in graph.nodes[node]:
            del graph.nodes[node]['epoch']

    for i, group in enumerate(groups):
        for node in group:
            graph.nodes[(node,)]['epoch'] = i

    def visit(node: int):
        if 'epoch' in graph.nodes[node]:
            return
        children = {c for c, _ in graph.in_edges(node)}
        heights = set()
        for child in children:
            if 'epoch' not in graph.nodes[child]:
                visit(child)
            heights.add(graph.nodes[child]['epoch'] + 1)
        graph.nodes[node]['epoch'] = max(heights, default=len(groups))

    for node in graph:
        visit(node)


def producers(graph: nx.DiGraph, nbunch) -> Set[int]:
    return {p for p, _ in graph.in_edges(nbunch)}


def nx_columnize(_graph: nx.DiGraph):
    graph = _graph.to_undirected()
    # graph = _graph

    epochs: Dict[int, List[int]] = defaultdict(list)

    for node in graph:
        epochs[graph.nodes[node]['epoch']].append(node)

    num_epochs = max(epochs.keys()) + 1

    # print('epochs:', epochs)

    # bipartite pieces, indexed by (source, target) epoch
    pieces: Dict[Tuple[int, int], nx.graph.Graph] = {}
    for i in range(num_epochs): # i = source epoch
        for j in range(i + 1, num_epochs): # j = target epoch
            # part1 = set(epochs[i])
            # part2 = consumers(_graph, epochs[i]).intersection(set(epochs[j]))

            part1 = set(epochs[j])
            part2 = producers(_graph, epochs[j]).intersection(epochs[i])

            # part2 = epochs[j]

            # print(f'Parts of {i, j}: {part1, part2}')

            # have to make a copy so that it can be modified independently
            bp_subgraph: nx.Graph = nx.Graph(graph.subgraph(part1 | part2))
            bp_subgraph.add_nodes_from(part1, bipartite=0)
            bp_subgraph.add_nodes_from(part2, bipartite=1)

            if bp_subgraph.number_of_edges() == 0:
                # nothing to see here, moving on...
                continue

            for x in part1:
                for y in part2:
                    weight = bp_subgraph.degree[x] + bp_subgraph.degree[y]
                    if bp_subgraph.has_edge(x, y):
                        # print(f'Weighting {x, y}')
                        bp_subgraph[x][y]['weight'] = weight

            # print(f'Putting {bp_subgraph.edges} in for {i, j}')
            pieces[i, j] = bp_subgraph
            # print(f'{i, j} weights: {bp_subgraph.edges(data=True)}')

    columns: DisjointSet[int] = DisjointSet()
    total_degree = 0

    for i, j in sorted(pieces.keys()):
        bp_piece = pieces[i, j]
        # print(f'Full bp piece {i, j}: {bp_piece.edges}')
        part = set(n for n, d in bp_piece.nodes(data=True) if d['bipartite'])

        # TODO: this is not the right condition for marking an edge 'unmatchable'
        ## also check if the edge connects an unmatched vertex to one already matched with something in the same epoch
        matchable_graph = nx.graphviews.subgraph_view(bp_piece, filter_edge=lambda u, v: not (columns.contains(u) and columns.contains(v)))
        
        # print(f'Marking edges {[(u, v) for u, v in bp_piece.edges if columns.contains(u) and columns.contains(v)]} as unmatchable')
        # print(f'{matchable_graph.edges} are all matchable')
        matching = nx.algorithms.max_weight_matching(matchable_graph, maxcardinality=True)


        # print(f'Querying weights for {matching}')
        weight = sum(bp_piece[u][v]['weight'] for u, v in matching)
        # print(f'Matching for {i, j}: {matching} (weight={weight})')
        

        for u, v in matching:
            assert not (columns.contains(u) and columns.contains(v)), (u, v)

            if columns.contains(u):
                columns.add_to(v, u)
            elif columns.contains(v):
                columns.add_to(u, v)
            else:
                columns.add(u)
                columns.add_to(v, u)

        columns.add(*filter(lambda p: not columns.contains(p), part))

        rotation_graph = nx.graphviews.subgraph_view(graph, filter_edge=lambda u, v: (u, v) not in matching and (v, u) not in matching)

        total_degree += max(rotation_graph.degree(), key=lambda n: n[1])[1]

    for i, col in enumerate(columns.all_classes()):
        for node in col:
            _graph.nodes[node]['column'] = i

    return columns


def rotation_cost(graph: nx.DiGraph, debug=False):
    spans: Dict[int, Set[int]] = defaultdict(set)
    for v1, v2 in graph.edges:
        span = graph.nodes[v2]['column'] - graph.nodes[v1]['column']
        if span == 0:
            continue
        src = graph.nodes[v1]['epoch']
        spans[src].add(span)

    cost = sum(map(len, spans.values()))
    if debug:
        print(f'Spans: {spans}; {cost}')

    return cost, spans


def permute(graph, num_cols, num_epochs):
    n1 = randint(0, num_cols - 1)
    n2 = randint(0, num_cols - 1)
    epochs = set(filter(lambda _: random() < 0.5, range(num_epochs)))

    if n1 == n2:
        return permute(graph, num_cols, num_epochs)
        
    s1 = {n for n, d in graph.nodes(data=True) if d['column'] == n1 and d['epoch'] in epochs}
    s2 = {n for n, d in graph.nodes(data=True) if d['column'] == n2 and d['epoch'] in epochs}

    if not s1 and not s2:
        return permute(graph, num_cols, num_epochs)

    return s1, s2, n1, n2


def lane_placement(graph: nx.DiGraph, t=10, beta=0.05, rounds=10000):
    current, _ = rotation_cost(graph)
    num_cols = 1 + max(d for _, d in graph.nodes(data='column'))
    num_epochs = 1 + max(d for _, d in graph.nodes(data='epoch'))

    if num_cols == 1:
        return current

    best_cost = current
    best_graph = nx.DiGraph(graph)

    for _ in range(rounds):
        # update temperature
        t /= (1 + t * beta)

        # generate candidate solution
        s1, s2, n1, n2 = permute(graph, num_cols, num_epochs)
        graph.add_nodes_from(s1, column=n2)
        graph.add_nodes_from(s2, column=n1)
        

        new_cost, _ = rotation_cost(graph)

        # print(f'Trying to permute {n1, n2} (acceptance = {min(100 * exp((current - new_cost) / t), 100)}%)')
        
        if new_cost < current or random() < exp((current - new_cost) / t):
            # print(f'\tCost {current} -> {new_cost}')
            current = new_cost
            
            # print('\taccepting!')
            # orig[n1], orig[n2] = orig[n2], orig[n1]
        else:
            graph.add_nodes_from(s1, column=n1)
            graph.add_nodes_from(s2, column=n2)

        if current < best_cost:
            best_cost = current
            best_graph = nx.DiGraph(graph)

    graph.update(best_graph)
    return best_cost


def contract_edge(graph: nx.DiGraph, edge):
    u, v = edge
    contracted = nx.contracted_edge(graph, edge, self_loops=False)
    return nx.relabel_nodes(contracted, {u: u + v}, copy=False)


def iterate_relax_schedule(graph: nx.DiGraph, groups: List[Set[int]], max_iter=10, max_edges=5, sample_freq=0.3):
    # setup: add metadata to the graph
    grade_nx_graph(graph, groups)
    nx_columnize(graph)
    
    # anneal the cells into a good column arrangement
    base_cost = lane_placement(graph)

    for _ in range(max_iter):
        # annotate for cross edges, used to find contraction candidates
        ann = defaultdict(set) 
        for u, v in graph.edges:
            src = graph.nodes[u]['epoch']
            span = graph.nodes[v]['column'] - graph.nodes[u]['column']
            
            if span == 0: continue
            if src < len(groups): continue
            
            ann[src, span].add((u, v))

        # sort annotations by which ones appear the least frequently (corresponds to good candidates to contract)
        # then iterate through the edges in that order, stopping at max_edges
        edges_to_try = sum((list(ann[a]) for a in sorted(ann.keys(), key=lambda a:len(ann[a]))), [])[:max_edges]
        print(f'Trying contracting {len(edges_to_try)} different edges...')
        options = [(base_cost, graph)]

        for edge in edges_to_try:
            contracted = contract_edge(graph, edge)
            grade_nx_graph(contracted, groups)
            contracted_cost = lane_placement(contracted)

            if contracted_cost <= base_cost:
                options.append((contracted_cost, contracted))

        print(f'{len(options) - 1} option(s) better than (or equal to) the baseline!')

        if len(options) == 1:
            print('Ending...')
            # none of the contraction options were better than the baseline, so exit out now
            break

        # otherwise, set the new graph to the current best and start over
        base_cost, graph = min(options)

    return graph, base_cost


def bfs_relax_schedule(graph: nx.DiGraph, groups: List[Set[int]], max_edges=10, max_iter=20):
    # compute initial metadata
    grade_nx_graph(graph, groups)
    nx_columnize(graph)

    # anneal into a good column arrangement
    min_cost = lane_placement(graph, t=50, beta=0.01, rounds=50000)
    best_graph = graph

    queue = [graph] # queue of schedules to anneal

    for i in range(max_iter):
        if not len(queue):
            print('No more graphs to try!')
            break

        print(f'Iteration {i}/{max_iter}: {len(queue)} graphs left in the queue!')

        cur = queue.pop(0)

        # annotate cross edges, used to find contraction candidates
        ann = defaultdict(set)
        for u, v in cur.edges:
            src = cur.nodes[u]['epoch']
            span = cur.nodes[v]['column'] - cur.nodes[u]['column']

            if span == 0: continue
            if src < len(groups): continue

            ann[src, span].add((u, v))

        # sort annotations by which ones appear the least frequently (good candidates to contract)
        # then iterate through edges in that order, stopping at max_edges
        edges_to_try = sum((list(ann[a]) for a in sorted(ann.keys(), key=lambda a:len(ann[a]))), [])[:max_edges]
        print(f'Trying contracting {len(edges_to_try)} different edges...')

        all_candidate_edges = set().union(*ann.values())

        costs_this_iter = []
        contracted_graphs = []
        for edge in edges_to_try:
        # for _ in range(max_edges):
            # edges_to_contract = list(filter(lambda e: random() < 0.5, all_candidate_edges))
            # contracted = cur
            # num_contracted = 0
            # for edge in edges_to_contract:
            #     try:
            #         contracted = contract_edge(contracted, edge)
            #         num_contracted += 1
            #     except ValueError:
            #         pass
            contracted = contract_edge(cur, edge)
            # print(f'Contracted {num_contracted} edges')
            grade_nx_graph(contracted, groups)
            contracted_cost = lane_placement(contracted)

            if contracted_cost > min_cost:
                print(f'\t(failed to beat {min_cost}, skipping this one)')
                continue
            print('\tBetter than or equal to the baseline!')
            costs_this_iter.append(contracted_cost)
            contracted_graphs.append(contracted)

        if not costs_this_iter:
            continue
        min_cost, best_graph_idx = min(zip(costs_this_iter, range(len(costs_this_iter))))
        best_graph = contracted_graphs[best_graph_idx]
        queue += contracted_graphs

    return best_graph, min_cost


def schedule_height(graph: nx.DiGraph, debug=False):
    cells = defaultdict(lambda: defaultdict(tuple))

    for node in graph:
        cells[graph.nodes[node]['epoch']][graph.nodes[node]['column']] += node

    columns = defaultdict(tuple)
    for node in graph:
        columns[graph.nodes[node]['column']] += node


    instr_counts = sum((reduce(lambda x, y: x | y, (Counter(graph.graph['ops'][instr] for instr in column) for column in epoch.values())) for epoch in cells.values()), Counter())
    cost = sum(COSTS_PER_ROTATE[op] * count for op, count in instr_counts.items())
    if debug:
        print(f'Instruction counts: {instr_counts}; {cost}')

    return cost

def anneal_relax_schedule(graph: nx.DiGraph, groups: List[Set[int]], t=20, beta=0.001, rounds=100, plot=False, max_restarts=None):
    # initial metadata
    grade_nx_graph(graph, groups)
    nx_columnize(graph)

    # anneal into a good column arrangement
    current_cost = lane_placement(graph, t=50, beta=0.001, rounds=50000)
    current_cost += schedule_height(graph)

    cur = nx.DiGraph(graph)

    best_cost = current_cost
    best_graph = nx.DiGraph(graph)

    already_visited = set()

    cost_history = []
    num_restarts = 0

    for round in range(rounds):
        t /= (1 + t * beta)

        # generate candidate solution
        ann = defaultdict(set)
        for u, v in cur.edges:
            src = cur.nodes[u]['epoch']
            span = cur.nodes[v]['column'] - cur.nodes[u]['column']

            if span == 0: continue
            if src < len(groups): continue

            ann[src, span].add((u, v))

        all_candidate_edges = list(set().union(*ann.values()) - already_visited)
        if not all_candidate_edges:
            if max_restarts and num_restarts >= max_restarts:
                break
            cur = nx.DiGraph(best_graph)
            current_cost = best_cost
            already_visited = set()
            num_restarts += 1
            continue
        # all_candidate_edges.sort()
        edge_to_contract = choice(all_candidate_edges)
        
        raw_contracted = contract_edge(cur, edge_to_contract)
        contracted = nx.condensation(raw_contracted) # candidate solution, condense any newly created SCCs to keep acyclic

        for node in contracted:
            contracted.nodes[node]['column'] = raw_contracted.nodes[next(iter(contracted.nodes[node]['members']))]['column']

        contracted.graph['ops'] = cur.graph['ops']

        relabeling = {num : sum(contracted.nodes[num]['members'], ()) for num in contracted}
        contracted = nx.relabel_nodes(contracted, relabeling)

        already_visited.add(edge_to_contract)
        
        # compute the new estimated (sub-annealed) cost
        grade_nx_graph(contracted, groups)
        contracted_cost = lane_placement(contracted)
        contracted_cost += schedule_height(contracted)

        # accept/reject the solution
        if contracted_cost < current_cost or random() < exp((current_cost - contracted_cost) / t):
            # accept!
            current_cost = contracted_cost
            cur = nx.DiGraph(contracted)
            already_visited = set()

        if current_cost < best_cost:
            best_cost = current_cost
            best_graph = nx.DiGraph(cur)

        cost_history.append(best_cost)

        print(f'Round {round}/{rounds}: current cost: {current_cost} (best seen = {best_cost}); prob of +1 cost = {exp(-1 / t) * 100:.1f}%')

    if plot:
        from matplotlib import pyplot as plt
        plt.plot(cost_history)
        plt.show()


    print('FINISHED ANNEALING')
    print('Final cost accounting:')
    rotation_cost(best_graph, debug=True)
    schedule_height(best_graph, debug=True)

    return best_graph, best_cost


def get_stages(graph: nx.DiGraph) -> Generator[Tuple[int], None, None]:
    cur_stage = 0
    while True:
        stage = ()
        for node in graph.nodes:
            if graph.nodes[node]['epoch'] == cur_stage:
                stage += node
        if not stage:
            break
        yield stage
        cur_stage += 1


def get_lanes(graph: nx.DiGraph, warp_size: int) -> List[int]:
    lanes = [0] * (1 + max(filter(lambda n: isinstance(n, int), sum(graph.nodes, ()))))
    for node in graph.nodes:
        for instr in node:
            # print(instr)
            lanes[instr] = graph.nodes[node]['column']

    return lanes
        

def vectorize(comp: CompilerV2):
    # compute the schedule
    loaded_groups = [{comp.loaded_regs[g] for g in group} for group in comp.input_groups]
    graph = instr_sequence_to_nx_graph(comp.code)
    actual_instrs = list(filter(lambda n: all(isinstance(m, int) for m in n), graph.nodes))
    graph = nx.DiGraph(nx.subgraph(graph, actual_instrs))

    relaxed_schedule, _ = anneal_relax_schedule(graph, loaded_groups, t=20, beta=0.001, rounds=200)

    print('Column mapping:')
    for node in relaxed_schedule.nodes:
        print(node, relaxed_schedule.nodes[node]['column'])

    # shift to start at column 1 :)
    min_column = min(relaxed_schedule.nodes[node]['column'] for node in relaxed_schedule)
    for node in relaxed_schedule.nodes:
        relaxed_schedule.nodes[node]['column'] -= min_column


    warp_size = max(relaxed_schedule.nodes[node]['column'] for node in relaxed_schedule) + 1
    lanes = get_lanes(relaxed_schedule, warp_size)

    vector_program: List[VecInstr] = []
    schedule = [0] * len(comp.code)
    for stage in get_stages(relaxed_schedule):
        stage_instrs = [comp.code[i] for i in stage]
        stage_sched = synthesize_schedule(stage_instrs, warp_size)
        for s, i in zip(stage_sched, stage_instrs):
            schedule[i.dest.val] = s + len(vector_program)
        vector_program += build_vector_program(stage_instrs, lanes, stage_sched)

    active_lanes = [[] for _ in range(max(schedule) + 1)]
    for instr in comp.code:
        active_lanes[schedule[instr.dest.val]].append(lanes[instr.dest.val])
    # print(f'Active lanes: {active_lanes}')
    inv_schedule = [[-1] * (max(lanes) + 1) for _ in range(max(schedule) + 1)]
    for instr in comp.code:
        inv_schedule[schedule[instr.dest.val]][lanes[instr.dest.val]] = instr.dest.val

    print(relaxed_schedule.nodes)

    return codegen(vector_program, relaxed_schedule, lanes, schedule, warp_size)


# coyote = coyote_compiler()

# @coyote.define_circuit(a=matrix(3, 3), b=matrix(3, 3))
# def matmul(a, b):
#     return [recursive_sum([a[i][k] * b[k][j] for k in range(len(a))]) for i in range(len(a)) for j in range(len(a))]

# @coyote.define_circuit(sig=vector(4), ker=vector(2))
# def conv(sig, ker):
#     output = []
#     for offset in range(len(sig) - len(ker) + 1):
#         output.append(recursive_sum([sig[offset + i] * ker[i] for i in range(len(ker))]))
#     return output


# @coyote.define_circuit(xs=vector(3), ys=vector(3))
# def distances(xs, ys):
#     return [(x - y) * (x - y) for x in xs for y in ys]


# def cond(b, true, false):
#     return b * true + (Var('1') + b) * false

# @coyote.define_circuit(c12=scalar(), c23=scalar(), c13=scalar(), o123=scalar(), o132=scalar(), o213=scalar(), o231=scalar(), o312=scalar(), o321=scalar())
# def sort_3(c12, c23, c13, o123, o132, o213, o231, o312, o321):
#     return cond(c12, 
#                 (cond(c23, 
#                     o123,
#                     cond(c13, o132, o312))), 
#                 (cond(c13,
#                     o213,
#                     cond(c23, o231, o321))))


# @coyote.define_circuit(cs=vector(3), os=vector(6))
# def sort_3_packed(cs, os):
#     return cond(cs[0], 
#                 (cond(cs[1], 
#                     os[0],
#                     cond(cs[2], os[1], os[4]))), 
#                 (cond(cs[2],
#                     os[2],
#                     cond(cs[1], os[3], os[5]))))


# @coyote.define_circuit(a=scalar(), b=scalar())
# def func(a, b):
#     return a * b + a + b


# @coyote.define_circuit(v1=vector(4), v2=vector(4))
# def dot_product(v1, v2):
#     return recursive_sum([a * b for a, b in zip(v1, v2)])


# COYOTE_VERSION = 2
# BENCHMARK = 'distances'

# if COYOTE_VERSION == 1:
#     scalar_code = coyote.instantiate(BENCHMARK)
#     vector_code, _ = coyote.vectorize()
# elif COYOTE_VERSION == 2:

#     groups, outputs = coyote.get_outputs(BENCHMARK)

#     # comp = Compiler({}, input_groups=groups)
#     comp = CompilerV2(groups)
#     tops = []
#     for out in outputs:
#         print(out)
#         tops.append(comp.compile(out))


#     # calc = SimilarityCalculator(comp.code)
#     # calc.calculate(tops)

#     scalar_code = list(map(str, comp.code))
#     vector_code = vectorize(comp)

# print('\n'.join(scalar_code))
# print('=' * 20)
# print('\n'.join(vector_code))