from collections import defaultdict
from random import seed
from typing import Generator, List, Tuple

import networkx as nx

from .codegen import build_vector_program, codegen
from .coyote_ast import CompilerV2
from .schedule_graph import instr_sequence_to_nx_graph
from .search.protoschedule import pq_relax_schedule
from .synthesize_schedule import VecSchedule, synthesize_schedule

seed(1)



def get_stages(graph: nx.DiGraph) -> Generator[Tuple[int], None, None]:
    cur_stage = 0
    
    epoch_grouping = defaultdict(set)
    for node in graph.nodes:
        epoch_grouping[graph.nodes[node]['epoch']].add(node)
        
    # print(f'Epoch grouping: {epoch_grouping}')
    
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

def vectorize(comp: CompilerV2, lanes_out=[], sched_out=[], extra_force_lanes: dict[int, int]={}):
    loaded_groups = [set().union(*(comp.loaded_regs[g] for g in group)) for group in comp.input_groups]

    loaded_lanes = {next(iter(comp.loaded_regs[g])): comp.force_lanes[g] for g in comp.force_lanes} | extra_force_lanes
    
    graph = instr_sequence_to_nx_graph(comp.code)
    actual_instrs = list(filter(lambda n: all(isinstance(m, int) for m in n), graph.nodes))
    graph = nx.DiGraph(nx.subgraph(graph, actual_instrs))

    relaxed_schedule = pq_relax_schedule(graph, loaded_groups, loaded_lanes, rounds=200).graph

    # shift to start at column 1 :)
    min_column = min(relaxed_schedule.nodes[node]['column'] for node in relaxed_schedule)
    for node in relaxed_schedule.nodes:
        relaxed_schedule.nodes[node]['column'] -= min_column


    warp_size = max(relaxed_schedule.nodes[node]['column'] for node in relaxed_schedule) + 1
    lanes = get_lanes(relaxed_schedule, warp_size)

    vector_program: List[VecSchedule] = []
    schedule = [0] * len(comp.code)
    for stage in get_stages(relaxed_schedule):
        stage_instrs = [comp.code[i] for i in stage]
        stage_sched = synthesize_schedule(stage_instrs, warp_size, lanes)
        for s, i in zip(stage_sched, stage_instrs):
            assert isinstance(i.dest.val, int)
            schedule[i.dest.val] = s + len(vector_program)
        vector_program += build_vector_program(stage_instrs, lanes, stage_sched)

    active_lanes: List[List[int]] = [[] for _ in range(max(schedule) + 1)]
    for instr in comp.code:
        assert isinstance(instr.dest.val, int)
        active_lanes[schedule[instr.dest.val]].append(lanes[instr.dest.val])

    inv_schedule = [[-1] * (max(lanes) + 1) for _ in range(max(schedule) + 1)]
    for instr in comp.code:
        assert isinstance(instr.dest.val, int)
        inv_schedule[schedule[instr.dest.val]][lanes[instr.dest.val]] = instr.dest.val

    lanes_out[:] = lanes
    sched_out[:] = schedule

    return codegen(vector_program, relaxed_schedule, lanes, schedule, warp_size)