from collections import Counter, defaultdict
from dataclasses import dataclass, field
from functools import reduce
from heapq import heappop, heappush
from typing import Optional, cast

from ..schedule_graph import grade_nx_graph, nx_columnize
from .lane_placement import lane_placement

import networkx as nx


MUL_PER_ROTATE = 1
ADD_PER_ROTATE = 0.1

COSTS_PER_ROTATE = defaultdict(int, {'+': ADD_PER_ROTATE, '*': MUL_PER_ROTATE, '-': ADD_PER_ROTATE})


def contract_edge(graph: nx.DiGraph, edge):
    u, v = edge
    contracted = nx.contracted_edge(graph, edge, self_loops=False)
    return nx.relabel_nodes(contracted, {u: u + v}, copy=False)

def schedule_height(graph: nx.DiGraph, debug=False):
    cells: dict[int, dict[int, tuple]] = defaultdict(lambda: defaultdict(tuple))

    for node in graph:
        cells[graph.nodes[node]['epoch']][graph.nodes[node]['column']] += node

    columns: dict[int, tuple] = defaultdict(tuple)
    for node in graph:
        columns[graph.nodes[node]['column']] += node


    instr_counts: Counter = sum((reduce(lambda x, y: x | y, (Counter(graph.graph['ops'][instr] for instr in column) for column in epoch.values())) for epoch in cells.values()), Counter())
    cost = sum(COSTS_PER_ROTATE[op] * count for op, count in instr_counts.items())
    if debug:
        print(f'Instruction counts: {instr_counts}; {cost}')

    return cost



def pq_relax_schedule(graph: nx.DiGraph, input_groups: list[set[int]], output_groups: list[set[int]], force_lanes: dict[int, int], rounds=200):
    @dataclass(order=True)
    class schedule:
        cost: int | float
        graph: nx.DiGraph=field(compare=False)
        edges: Optional[list[tuple]]=field(compare=False)

    input_epochs, output_epochs = grade_nx_graph(graph, input_groups, output_groups)
    nx_columnize(graph, force_lanes)
    # print(force_lanes)
    # print('AFTER COLUMNIZING')
    # print(graph.nodes(data=True))
    # print(f'Original rotation cost: {rotation_cost(graph)}')
    new_data = {}
    for reg, lane in force_lanes.items():
        # print(f'Setting {graph.nodes[reg,]["column"]} to {lane}')
        col_num = graph.nodes[reg,]['column']
        new_data.update({n: lane for n, d in graph.nodes(data=True) if d['column'] == col_num})
        # graph.nodes[reg,]['column'] = lane
    nx.set_node_attributes(graph, new_data, name='column')

    # print('FIRST FIX')
    # print(graph.nodes(data=True))

    cost_history = []
    best_history = []

    # print(rotation_cost(graph))
    # input()
    current_cost = lane_placement(graph, force_lanes, t=50, beta=0.001, rounds=50000)
    current_cost += schedule_height(graph)
    
    # print('ONE ROUND OF SA')
    # print(graph.nodes(data=True))
    # print(rotation_cost(graph))
    # input()
    
    for reg, lane in force_lanes.items():
        # print(f'Setting {graph.nodes[reg,]["column"]} to {lane}')
        # col_num = graph.nodes[reg,]['column']
        # new_data = {n: lane for n, d in graph.nodes(data=True) if d['column'] == col_num}
        graph.nodes[reg,]['column'] = lane
        # nx.set_node_attributes(graph, new_data, name='column')

    # print('SECOND FIX')
    # print(graph.nodes(data=True))
    best = schedule(cost=current_cost, graph=nx.DiGraph(graph), edges=None)
    
    pqueue: list[schedule] = []
    heappush(pqueue, schedule(cost=best.cost, graph=best.graph, edges=None))
    for r in range(rounds):
        if not len(pqueue):
            # print('No more graphs to try!')
            break

        cur = heappop(pqueue)

        best_history.append(best.cost)
        cost_history.append(cur.cost)
        # if len(pqueue):
        #     print(f'Round {r}/200: exploring {cur.cost}{" (new best!)" if cur < best else ""}')
        if cur < best:
            best = schedule(cost=cur.cost, graph=nx.DiGraph(cur.graph), edges=None)

        if cur.edges is None:
            # generate all candidate solutions
            cross_edges = set()
            for u, v in cur.graph.edges:
                src = cur.graph.nodes[u]['epoch']
                dst = cur.graph.nodes[v]['epoch']
                span = cur.graph.nodes[v]['column'] - cur.graph.nodes[u]['column']

                if span == 0: continue
                if src in input_epochs: continue
                if dst in output_epochs: continue
                cross_edges.add((u, v))

            cur.edges = list(cross_edges)
        
        if not len(cur.edges):
            continue
            
        edge_to_contract = None
        # grab an edge, remove it from the list, and add its contraction to the queue
        while True:
            if not cur.edges:
                break
            edge_to_contract = cur.edges.pop()
            
            left_fixed = set(edge_to_contract[0]).intersection(set(force_lanes.keys()))
            right_fixed = set(edge_to_contract[1]).intersection(set(force_lanes.keys()))
            if left_fixed and right_fixed and force_lanes[next(iter(left_fixed))] != force_lanes[next(iter(right_fixed))]:
                continue
            break
        if edge_to_contract is None: # none of the candidates were free
            continue
        
        # for edge_to_contract in cross_edges:
            # print(f'\tedge {edge_to_contract}...')
        raw_contracted = contract_edge(cur.graph, edge_to_contract)
        contracted = cast(nx.DiGraph, nx.condensation(raw_contracted))

        for node in contracted:
            fixed = set(sum(contracted.nodes[node]['members'], ())).intersection(set(force_lanes.keys()))
            if fixed:
                contracted.nodes[node]['column'] = force_lanes[next(iter(fixed))]
            else:
                contracted.nodes[node]['column'] = raw_contracted.nodes[next(iter(contracted.nodes[node]['members']))]['column']

        contracted.graph['ops'] = cur.graph.graph['ops']
    
        relabeling = {num : sum(contracted.nodes[num]['members'], ()) for num in contracted}
        contracted = nx.relabel_nodes(contracted, relabeling)

        input_epochs, output_epochs = grade_nx_graph(contracted, input_groups, output_groups)
        contracted_cost = lane_placement(contracted, force_lanes, t=50, beta=0.001, rounds=20000)
        contracted_cost += schedule_height(contracted)

        heappush(pqueue, schedule(cost=contracted_cost, graph=nx.DiGraph(contracted), edges=None))
        if len(cur.edges): # if there are still unexplored edges
            heappush(pqueue, schedule(cost=cur.cost, graph=nx.DiGraph(cur.graph), edges=cur.edges[:])) # put this back into the queue

    """from matplotlib import pyplot as plt
    plt.plot(cost_history)
    plt.plot(best_history)
    plt.show()"""

    with open('trace.csv', 'w') as f:
        f.write(','.join(map(str, cost_history)) + '\n')
        f.write(','.join(map(str, best_history)) + '\n')

    return best