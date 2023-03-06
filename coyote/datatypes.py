from dataclasses import dataclass
from typing import Callable, Set, Tuple, Type

from coyote_ast import Var

@dataclass
class matrix:
    rows: int
    cols: int
    replicate: bool = False

@dataclass
class vector:
    size: int
    replicate: bool = False

@dataclass
class scalar:
    pass


class indexer:
    def __init__(self, shape: Tuple[int], name_provider: Callable[[Tuple[int]], str]):
        self.shape = shape
        self.name_provider = name_provider
        
    def data_index(self, index: Tuple[int]):
        ...
        
        
class storage:
    def __init__(self, size: int, name_provider: Callable[[int], str]):
        self.size = size
        self.name = name_provider
        self.accessed: Set[str] = set()
        
    def _get(self, i: int) -> Var:
        ...
        
    def get(self, i: int) -> Var:
        if i >= self.size:
            raise IndexError('list index out of range')
        v = self._get(i)
        self.accessed.add(v.name)
        return v

class copy_storage(storage):
    def _get(self, i: int) -> Var:
        return Var(self.name(i))
    
class reuse_storage(storage):
    def __init__(self, size: int, name_provider: Callable[[int], str]):
        super().__init__(size, name_provider)
        self.data = [Var(self.name(i)) for i in range(self.size)]
        
    def _get(self, i: int) -> Var:
        return self.data[i]
    

class shape:
    dims: int
    def get_index(self, idx: Tuple[int]) -> int:
        ...
        

class partial_indexer:
    def __init__(self, sh: shape):
        self.shape = sh
        self.indices = []
        
    def __getitem__(self, i):
        return partial_indexer(self.shape, self.indices + [i])
    
    def get(self):
        if len(self.indices)

class row_major_matrix(shape):
    def __init__(self, name: str, rows: int, cols: int, storage_cls: Type[storage]):
        self.rows = rows
        self.cols = cols
        self.dims = 2
        
        self.storages = [storage_cls(self.cols, lambda c: f'{name}:{i};{c}') for i in range(self.rows)]

    def get_index(self, idx: index) -> Var:
        assert len(idx.dims) == 2