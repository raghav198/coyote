from collections import defaultdict
from dataclasses import dataclass, field
from random import seed
from typing import Generator, List, Tuple

import networkx as nx

from .better_rotations import better_rotations

from .codegen import Schedule, codegen, VecInstr
from .coyote_ast import CompilerV2
from .schedule_graph import instr_sequence_to_nx_graph
from .search.blend_alignment import relax_blends
from .search.protoschedule import pq_relax_schedule
from .synthesize_schedule import fast_align, synthesize_alignment

seed(1)


@dataclass(kw_only=True)
class CodeObject:
    """Object containing Coyote IR and statistics useful for analysis
    """
    instructions: list[VecInstr] = field(default_factory=list)
    
    lanes: list[int] = field(default_factory=list)
    alignment: list[int] = field(default_factory=list)
    
    vector_width: int = 0
    max_rotation: int = 0
    min_rotation: int = 0
    

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

def vectorize(comp: CompilerV2, extra_force_lanes: dict[int, int]={}, output_groups: list[set[int]]=[], search_rounds=200):
    input_groups = [set().union(*(comp.loaded_regs[g] for g in group)) for group in comp.input_groups]

    loaded_lanes = {next(iter(comp.loaded_regs[g])): comp.force_lanes[g] for g in comp.force_lanes} | extra_force_lanes
    
    graph = instr_sequence_to_nx_graph(comp.code)

    actual_instrs = list(filter(lambda n: all(isinstance(m, int) for m in n), graph.nodes))
    graph = nx.DiGraph(nx.subgraph(graph, actual_instrs))

    protoschedule = pq_relax_schedule(graph, input_groups, output_groups, loaded_lanes, rounds=search_rounds).graph

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
        # stage_align = synthesize_alignment(stage_instrs, warp_size, lanes)
        stage_align = fast_align(stage_instrs, warp_size, lanes)
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
    print('before relaxing blends:')
    for line in schedule:
        print(line)
        
    print(f'lanes: {schedule.lanes}')
    print(f'alignment: {schedule.alignment}')
    
    blend_relaxed_schedule = relax_blends(schedule)

    print('after relaxing blends:')
    for line in blend_relaxed_schedule:
        print(line)

    print(f'lanes: {blend_relaxed_schedule.lanes}')
    print(f'alignment: {blend_relaxed_schedule.alignment}')
    
    generated_code = codegen(blend_relaxed_schedule)
    better_code, max_rotation, min_rotation = better_rotations(generated_code, max(blend_relaxed_schedule.lanes) + 1)
    
    return CodeObject(instructions=better_code, lanes=blend_relaxed_schedule.lanes, 
                      alignment=blend_relaxed_schedule.alignment,
                      vector_width=max(blend_relaxed_schedule.lanes) + 1, 
                      max_rotation=max_rotation, min_rotation=min_rotation)
    
    
def vectorize_cached(cached_schedule: Schedule):
    # blend_relaxed_schedule = relax_blends(cached_schedule)
    generated_code = codegen(cached_schedule)
    better_code, max_rotation, min_rotation = better_rotations(generated_code, max(cached_schedule.lanes) + 1)
    return CodeObject(instructions=better_code, lanes=cached_schedule.lanes, 
                      alignment=cached_schedule.alignment, vector_width=max(cached_schedule.lanes) + 1,
                      max_rotation=max_rotation, min_rotation=min_rotation)