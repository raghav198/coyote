from math import exp
from random import randint, random
import networkx as nx
from collections import defaultdict


def rotation_cost(graph: nx.DiGraph, debug=False):
    spans: dict[int, set[int]] = defaultdict(set)
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


def lane_placement(graph: nx.DiGraph, force_lanes: dict[int, int], t=10, beta=0.05, rounds=10000):
    current, _ = rotation_cost(graph)
    num_cols = 1 + max(d for _, d in graph.nodes(data='column')) # type: ignore
    num_epochs = 1 + max(d for _, d in graph.nodes(data='epoch')) # type: ignore

    if num_cols == 1:
        return current

    best_cost = current
    best_graph = nx.DiGraph(graph)

    for _ in range(rounds):
        # update temperature
        t /= (1 + t * beta)

        # generate candidate solution
        s1, s2, n1, n2 = permute(graph, num_cols, num_epochs)
        # disallow changing lanes which have already been fixed
        fixed = set(force_lanes.keys())
        s1 = {n for n in s1 if not set(n).intersection(fixed)}
        s2 = {n for n in s2 if not set(n).intersection(fixed)}
        # s1 -= set(force_lanes.keys())
        # s2 -= set(force_lanes.keys())
        # apply permutation
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
