from typing import Any, Dict, List, Union

def this_refines(x : Union[int, str], y : List[int]):
    if x in y:
        print(x) # inferred type int here


def this_does_not(x: Union[int, str], y : Dict[int, Any], z: Dict[int, Any]):
    if x in list(y.keys()):
        print(x)
        print(z[x]) # inferred type int | str here