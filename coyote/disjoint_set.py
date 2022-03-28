from typing import Generic, List, Set, Dict, TypeVar, Generator

class ItemAlreadyPresent(Exception):
    pass

class ItemNotPresent(Exception):
    pass

T = TypeVar('T')
class DisjointSet(Generic[T]):
    def __init__(self):
        """Creates an empty DisjointSet data structure"""
        self.vertices: Set[T] = set()
        self.parent: Dict[T, T] = {}
        self.children: Dict[T, Set[T]] = {}

    def contains(self, item: T) -> bool:
        """
        :param item: T
        :return True if `item` is contained in an equivalence class, False otherwise
        """
        return item in self.vertices

    def add(self, *items: List[T]):
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

    def find(self, item: T) -> Set[T]:
        """
        :param item: T. Representative of an equivalence class.
        :return: Set of all items contained in the equivalence class represented by `item`.
        :raises ItemNotPresent if `item` is not  contained in the structure.
        """
        
        if not self.contains(item):
            raise ItemNotPresent(item)

        items = set().union(*(self.find(child) for child in self.children[item]))
        items.add(item)
        return items

    def all_classes(self) -> Generator[Set[T], None, None]:
        """
        :returns: A generator of equivalence classes of items
        """
        consumed = set()
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
    