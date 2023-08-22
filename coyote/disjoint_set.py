from copy import deepcopy
from math import ceil
from typing import Generic, Set, Dict, TypeVar, Generator

class ItemAlreadyPresent(Exception):
    pass

class ItemNotPresent(Exception):
    pass

T = TypeVar('T')
class DisjointSet(Generic[T]):
    def __init__(self):
        """Create a new empty DisjointSet
        """
        self.vertices: Set[T] = set()
        self.parent: Dict[T, T] = {}
        self.children: Dict[T, Set[T]] = {}
    
    
    def copy(self):
        """Return a deep copy of this DisjointSet
        Returns:
            DisjointSet[T]: deep copy of `self`
        """
        return deepcopy(self)
        
    def limit_classes(self, limit: int, mutually_disjoint: list[set[T]]=[]):

        classes = list(self.all_classes())
        if len(classes) <= limit:
            return
        class_index = {item: classes.index(self.find(item)) for group in mutually_disjoint for item in group}
        
        # decide how to allocate chunks
        which_chunk: list[int] = []
        cur_chunk = 0
        # print('Initial chunk allocation:')
        while max(which_chunk, default=-1) < limit - 1:
            # print(f'{max(which_chunk, default=-1)} vs {limit - 1} (current chunk #{cur_chunk})')
            size = ceil((len(classes) - len(which_chunk)) / (limit - (max(which_chunk, default=-1) + 1)))
            # print(f'Adding {size} more')
            which_chunk += ([cur_chunk] * size)
            cur_chunk += 1
            
        # for group in mutually_disjoint:
        #     print([which_chunk[class_index[item]] for item in group]) 
            
        all_chunks = set(which_chunk)
        for group in mutually_disjoint:
            group_chunks = []
            for item in group:
                # print(f'For item {item} (wants {which_chunk[class_index[item]]}), group_chunks={group_chunks}')
                if which_chunk[class_index[item]] in group_chunks:
                    # print(f'Chunk of {item} already allocated, switching...')
                    which_chunk[class_index[item]] = list(all_chunks - set(group_chunks))[0]
                group_chunks.append(which_chunk[class_index[item]])
                
        # for group in mutually_disjoint:
        #     print([which_chunk[class_index[item]] for item in group])
        
        chunks = []
        for i in range(limit):
            chunk_i = []
            for j, cls in enumerate(classes):
                if which_chunk[j] == i:
                    chunk_i.append(cls)
            chunks.append(chunk_i)
        # index = 0
        # while len(chunks) < limit:
        #     size = ceil((len(classes) - index) / (limit - len(chunks)))
        #     chunks.append(classes[index:index + size])
        #     which_chunk += ([len(chunks) - 1] * size)
        #     index += size
            
        
            
        for chunk in chunks:
            if not chunk:
                continue
            rep = list(chunk[0])[0]
            for cls in chunk:
                self.union(rep, list(cls)[0])

        
    def new_class(self, *items: T):
        """
        :param *items: List[T]. List of items to add to the DisjointSet
        :return None
        :raises ItemAlreadyPresent if any item is already contained in the structure
        
        Adds all items into the same fresh equivalence class
        """
        self.add(*items)
        for item in items[1:]:
            self.union(items[0], item)

    def contains(self, item: T) -> bool:
        """Test whether an item is contained in the DisjointSet

        Args:
            item (T): item to test for membership

        Returns:
            bool: True if `item` is contained in an equivalence class, False otherwise
        """
        return item in self.vertices

    def add(self, *items: T):
        """
        :param *items: List[T]. List of items to add to the DisjointSet
        :return None
        :raises ItemAlreadyPresent if any item is already contained in the structure.

        Creates a fresh equivalence class for each item added.
        """

        contained = filter(self.contains, items)
        for c in contained:
            raise ItemAlreadyPresent(c)

        for item in items:
            self.vertices.add(item)
            self.parent[item] = item
            self.children[item] = set()

    def rep(self, item: T) -> T:
        """
        :param item: T. Item to find a representative of.
        :return The canonical representative of the equivalence class containing `item`
        :raises ItemNotPresent if `item` is not contained in the structure
        """

        if not self.contains(item):
            raise ItemNotPresent(item)

        if self.parent[item] == item:
            return item
        self.children[self.parent[item]].remove(item)
        self.parent[item] = self.rep(self.parent[item])
        self.children[self.parent[item]].add(item)
        return self.parent[item]

    def union(self, item1: T, item2: T):
        """
        :param item1: T. Representative of the first equivalence class
        :param item2: T. Representative of the second equivalence class
        :return: None
        :raises ItemNotPresent if either `item1` or `item2` is not contained in the structure
        """
        root1 = self.rep(item1)
        root2 = self.rep(item2)
        if root1 == root2:
            return
        self.parent[root1] = root2
        self.children[root2].add(root1)

    def add_to(self, item: T, rep: T):
        """
        :param item: T. Item to add to the structure.
        :param rep: T. Representative of the equivalence class to add `item` to.
        :return: None
        :raises ItemNotPresent if `rep` is not contained in the structure.
        :raises ItemAlreadyPresent if `item` is already contained in the structure.

        Assigns `item` to a particular equivalence class when adding, instead of creating a new one.
        """
        self.add(item)
        self.union(item, rep)

    def find(self, item: T, ensure_rep=True) -> Set[T]:
        """
        :param item: T. Representative of an equivalence class.
        :return: Set of all items contained in the equivalence class represented by `item`.
        :raises ItemNotPresent if `item` is not  contained in the structure.
        """
        
        if not self.contains(item):
            raise ItemNotPresent(item)
        
        if ensure_rep:
            item = self.rep(item)

        items = set().union(*(self.find(child, ensure_rep=False) for child in self.children[item]))
        items.add(item)
        return items

    def all_classes(self) -> Generator[Set[T], None, None]:
        """
        :returns: A generator of equivalence classes of items
        """
        consumed: Set[T] = set()
        while True:
            remaining = list(self.vertices - consumed)
            if not remaining:
                break
            v = self.rep(remaining[0])
            equiv_class = self.find(v)
            consumed.update(equiv_class)
            yield equiv_class

    def is_equivalent(self, item1: T, item2: T) -> bool:
        """
        :param item1: T. First item
        :param item2: T. Second item
        :return: True if `item1` and `item2` are in the same equivalence class, False otherwise
        :raises ItemNotPresent if either `item1` or `item2` are not contained in the structure
        """
        rep1 = self.rep(item1)
        rep2 = self.rep(item2)
        return rep1 == rep2
    