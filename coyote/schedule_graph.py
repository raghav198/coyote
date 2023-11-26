from collections import defaultdict
from math import ceil
from typing import cast
import networkx as nx

from .coyote_ast import Instr
from .disjoint_set import DisjointSet

def instr_sequence_to_nx_graph(instrs: list[Instr]) -> nx.DiGraph:
    graph = nx.DiGraph()
    graph.graph['ops'] = {}
    for instr in instrs:
        graph.graph['ops'][instr.dest.val] = instr.op
        # if instr.op == '~':
        #     continue
        if instr.op == '~' and not (instr.lhs.reg and instr.rhs.reg):
            continue
        graph.add_edge((instr.lhs.val,), (instr.dest.val,))
        graph.add_edge((instr.rhs.val,), (instr.dest.val,))
        
    return graph


def limit_width(graph: nx.DiGraph, width: int):
    
    # sanity check: violations?
    for u, v in graph.edges:
        if graph.nodes[u]['epoch'] == graph.nodes[v]['epoch']:
            print(f'[ERROR] {u}, {v} on same epoch despite edge!')
            quit()
        
    
    current_epoch: int = 0
    number_of_epochs = 1 + max(d for _, d in graph.nodes(data='epoch')) # type: ignore
    update_values: dict[tuple[int], dict[str, int]] = {}
    for epoch in range(number_of_epochs):
        nodes_at_epoch = [node for node, data in graph.nodes(data=True) if data['epoch'] == epoch]
        chunks = [nodes_at_epoch[i * width : (i + 1) * width] for i in range(ceil(len(nodes_at_epoch) / width))]
        for chunk in chunks:
            update_values.update({node: {'epoch': current_epoch} for node in chunk})
            current_epoch += 1
            
    nx.set_node_attributes(graph, values=update_values)
        
    # sanity check: violations?
    for u, v in graph.edges:
        # print(u, v, graph.nodes[u]['epoch'], graph.nodes[v]['epoch'])
        
        if graph.nodes[u]['epoch'] == graph.nodes[v]['epoch']:
            print(f'[ERROR] {u}, {v} on same epoch despite edge!')
            quit()
        
        
    return graph

def grade_nx_graph(graph: nx.DiGraph, input_groups: list[set[int]], output_groups: list[set[int]], debug=False):
    # print(f'grading; outputs = {output_groups}')
    input_epochs: set[int] = set()
    output_epochs: set[int] = set()
    for node in graph:
        if 'epoch' in graph.nodes[node]:
            del graph.nodes[node]['epoch']

    for i, group in enumerate(input_groups):
        # print(f'setting input {group} to {i}')
        for node in group:
            graph.nodes[(node,)]['epoch'] = i
            input_epochs.add(i)

    def visit(node: tuple[int]):
        if 'epoch' in graph.nodes[node]:
            return
        if debug: print(f'visiting {node}')
        if any(set(node).intersection(group) for group in output_groups):
            if debug: print('output, skipping')
            return
        children = {c for c, _ in graph.in_edges(node)}
        if debug: print(f'children: {children}')
        heights = set()
        for child in children:
            if 'epoch' not in graph.nodes[child]:
                visit(child)
            try:
                heights.add(graph.nodes[child]['epoch'] + 1)
            except KeyError as ke:
                if debug:
                    raise ke from ke
                grade_nx_graph(graph, input_groups, output_groups, debug=True)
        # print(f'setting intermediate {node} to {max(heights | {len(input_groups)})}')
        graph.nodes[node]['epoch'] = max(heights | {len(input_groups)})

    for node in graph:
        visit(node)
        
    # print(graph.nodes(data='epoch'))
    max_epoch = max(dict(graph.nodes(data='epoch', default=-1)).values()) # type: ignore
        
    for i, group in enumerate(output_groups):
        for node in group:
            graph.nodes[(node,)]['epoch'] = i + max_epoch + 1
            output_epochs.add(i + max_epoch + 1)
            
            
    # print(1 + max(d for _, d in graph.nodes(data='epoch'))) # type: ignore
    # limit_width(graph, 210)
    # print(1 + max(d for _, d in graph.nodes(data='epoch'))) # type: ignore
    # input()
            
    return input_epochs, output_epochs

def producers(graph: nx.DiGraph, nbunch) -> set[int]:
    return {p for p, _ in graph.in_edges(nbunch)} # type: ignore


def nx_columnize(_graph: nx.DiGraph, force_lanes: dict[int, int]):
    # graph = nx.quotient_graph(_graph.to_undirected(), lambda u, v: u in force_lanes and v in force_lanes and force_lanes[u] == force_lanes[v])
    # graph = _graph
    graph: nx.Graph = cast(nx.Graph, _graph.to_undirected())

    epochs: dict[int, list[int]] = defaultdict(list)
    for node in graph:
        epochs[_graph.nodes[node]['epoch']].append(node)
        
    # for epoch in epochs:
    #     print(epoch, len(epochs[epoch]))
    # input()

    num_epochs = max(epochs.keys()) + 1

    # print('epochs:', epochs)
    

    # bipartite pieces, indexed by (source, target) epoch
    pieces: dict[tuple[int, int], nx.graph.Graph] = {}
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
    # print(pieces)
    columns: DisjointSet[tuple[int]] = DisjointSet()
    total_degree = 0
    
    preloaded: dict[int, set[tuple[int]]] = defaultdict(set)
    for node in force_lanes:
        preloaded[force_lanes[node]].add((node,))
    for group in preloaded.values():
        # print(f'Grouping {group} into a column')
        columns.new_class(*group)
        
    # print('in grading, the following are already put in columns:')
    # for cls in columns.all_classes():
    #     print(cls)

    for i, j in sorted(pieces.keys()):
        bp_piece = pieces[i, j]
        # print(f'Full bp piece {i, j}: {bp_piece.edges}')
        part = set(n for n, d in bp_piece.nodes(data=True) if d['bipartite'])

        # TODO: this is not the right condition for marking an edge 'unmatchable'
        ## also check if the edge connects an unmatched vertex to one already matched with something in the same epoch
        matchable_graph = nx.graphviews.subgraph_view(bp_piece, filter_edge=lambda u, v: not (columns.contains(u) and columns.contains(v)))
        # matchable_graph = nx.graphviews.subgraph_view(matchable_graph, filter_edge=lambda u, v: not (u in force_lanes and v in force_lanes and force_lanes[u] != force_lanes[v]))
        
        # print(f'Marking edges {[(u, v) for u, v in bp_piece.edges if columns.contains(u) and columns.contains(v)]} as unmatchable')
        # print(f'{matchable_graph.edges} are all matchable')
        matching = nx.algorithms.max_weight_matching(matchable_graph, maxcardinality=True)
        # print(len([n for n, d in matchable_graph.nodes(data=True) if d['bipartite'] == 0]))
        # print(len([n for n, d in matchable_graph.nodes(data=True) if d['bipartite'] == 1]))


        weight = sum(bp_piece[u][v]['weight'] for u, v in matching)
        # print(i, j, len(matching))
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
    # list(map(print, map(sorted, columns.all_classes())))
    # quit()
    
    # columns.limit_classes(210)
    
    for i, col in enumerate(columns.all_classes()):
        for node in col:
            _graph.nodes[node]['column'] = i

    return columns
