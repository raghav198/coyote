from typing import Dict, List, TypeVar


Node = TypeVar('Node')
Graph = Dict[Node, List[Node]]

class Edge(frozenset):
    def __new__(cls, v1, v2):
        return super().__new__(cls, {v1, v2})

    def __repr__(self):
        v1, v2 = self
        return f'{v1} -- {v2}'

def edges_on_path(path: List[Node]) -> List[Edge]:
    edges: List[Edge] = []
    for v1, v2 in zip(path[:-1], path[1:]):
        edges.append(Edge(v1, v2))
    return edges

def connect(graph: Graph[Node], v1: Node, v2: Node):
    graph[v1].append(v2)
    graph[v2].append(v1)
