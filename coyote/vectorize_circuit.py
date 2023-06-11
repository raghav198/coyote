from collections import defaultdict
from random import seed
from typing import Generator, List, Tuple

import networkx as nx

from .codegen import Schedule, codegen
from .coyote_ast import CompilerV2
from .schedule_graph import instr_sequence_to_nx_graph
from .search.blend_alignment import relax_blends
from .search.protoschedule import pq_relax_schedule
from .synthesize_schedule import synthesize_alignment

seed(1)



def get_stages(graph: nx.DiGraph) -> Generator[Tuple[int], None, None]:
    cur_stage = 0
    
    epoch_grouping = defaultdict(set)
    for node in graph.nodes:
        epoch_grouping[graph.nodes[node]['epoch']].add(node)
    
    while True:
        stage = ()
        for node in graph.nodes:
            if graph.nodes[node]['epoch'] == cur_stage:
                stage += node
        if not stage:
            break
        yield stage
        cur_stage += 1


def get_lanes(graph: nx.DiGraph) -> List[int]:
    lanes = [0] * (1 + max(filter(lambda n: isinstance(n, int), sum(graph.nodes, ()))))
    for node in graph.nodes:
        for instr in node:
            # print(instr)
            lanes[instr] = graph.nodes[node]['column']

    return lanes

def vectorize(comp: CompilerV2, lanes_out=[], align_out=[], extra_force_lanes: dict[int, int]={}):
    loaded_groups = [set().union(*(comp.loaded_regs[g] for g in group)) for group in comp.input_groups]

    loaded_lanes = {next(iter(comp.loaded_regs[g])): comp.force_lanes[g] for g in comp.force_lanes} | extra_force_lanes
    
    graph = instr_sequence_to_nx_graph(comp.code)
    actual_instrs = list(filter(lambda n: all(isinstance(m, int) for m in n), graph.nodes))
    graph = nx.DiGraph(nx.subgraph(graph, actual_instrs))

    protoschedule = pq_relax_schedule(graph, loaded_groups, loaded_lanes, rounds=200).graph

    # shift to start at column 1 :)
    min_column = min(protoschedule.nodes[node]['column'] for node in protoschedule)
    for node in protoschedule.nodes:
        protoschedule.nodes[node]['column'] -= min_column


    warp_size = max(protoschedule.nodes[node]['column'] for node in protoschedule) + 1
    lanes = get_lanes(protoschedule)

    program_length: int = 0
    alignment = [0] * len(comp.code)
    for stage in get_stages(protoschedule):
        stage_instrs = [comp.code[i] for i in stage]
        stage_align = synthesize_alignment(stage_instrs, warp_size, lanes)
        for s, i in zip(stage_align, stage_instrs):
            assert isinstance(i.dest.val, int)
            alignment[i.dest.val] = s + program_length
        program_length = max(alignment) + 1
        # vector_program += build_vector_program(stage_instrs, lanes, stage_align)

    active_lanes: List[List[int]] = [[] for _ in range(max(alignment) + 1)]
    for instr in comp.code:
        assert isinstance(instr.dest.val, int)
        active_lanes[alignment[instr.dest.val]].append(lanes[instr.dest.val])
        
    schedule = Schedule(lanes, alignment, comp.code)
    blend_relaxed_schedule = relax_blends(schedule)

    lanes_out[:] = blend_relaxed_schedule.lanes
    align_out[:] = blend_relaxed_schedule.alignment
    
    for line in blend_relaxed_schedule:
        print(line)

    return codegen(blend_relaxed_schedule)

    # return codegen(vector_program, lanes, alignment, warp_size)