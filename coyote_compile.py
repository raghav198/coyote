import argparse
from time import time
import os
from coyote import coyote_compiler
import importlib, pathlib
import fnmatch
from compile_to_bfv import compile_scalar, compile_vector


def get_coyote(path: str) -> coyote_compiler:
    module_name = pathlib.Path(path).stem
    module = importlib.import_module(module_name)

    coyotes = []

    for name, obj in module.__dict__.items():
        if name.startswith('__'): continue
        if isinstance(obj, coyote_compiler):
            coyotes.append(obj)

    if len(coyotes) > 1:
        raise ImportError(f'Source file {path} has multiple Coyote objects defined!')
    if not coyotes:
        raise ImportError(f'Source file {path} has no Coyote objects!')
    return coyotes[0]

def main():
    import sys
    sys.path.append(os.getcwd())
    parser = argparse.ArgumentParser(description='Compile Coyote programs')
    
    parser.add_argument('coyote_file', help='File containing Coyote program')
    
    action_group = parser.add_mutually_exclusive_group(required=True)
    action_group.add_argument('-l', '--list', action='store_true', help='List available benchmarks and exit')
    action_group.add_argument('-c', '--circuits', type=str, nargs='+', help='Compile the specified circuits')
    
    parser.add_argument('-o', '--output-dir', type=str, help='Where to place Coyote output', default='.')
    parser.add_argument('--backend-dir', type=str, help='Location of Coyote backend', default='./bfv_backend')
    parser.add_argument('--combine', action='store_true', help='Combine everything into a single circuit')

    cpp_group = parser.add_mutually_exclusive_group()
    cpp_group.add_argument('--no-cpp', action='store_true', help='Stop before generating C++')
    cpp_group.add_argument('--just-cpp', action='store_true', help='Use precompiled Coyote code to directly generate C++')
    
    parser.add_argument('-u', '--update-cmake', action='store_true', help='Update CMakeLists.txt with circuits')

    # TODO: expose some compiler options in the API (i.e. verbosity, turning features on/off, number of rounds, etc.) and then expose those here

    args = parser.parse_args()

    try:
        coyote = get_coyote(args.coyote_file)
    except ImportError as e:
        parser.error(f'{e}')
        return

    available = [func.__name__ for func in coyote.func_signatures]

    if args.list:
        print(f'Circuits available in {args.coyote_file}:')
        for func in available:
            print(f'* {func}')
        return

    output_dir = args.output_dir

    # for circuit in args.circuits:
    #     if circuit not in available:
    #         parser.error(f'Coyote file `{args.coyote_file}` does not define `{circuit}` as a circuit!')
     

    if args.combine:
        print('...no <3')
        return
    
    scalars: dict[str, list[str]] = {}
    vectors: dict[str, list[str]] = {}

    if not args.just_cpp and not os.path.exists(args.backend_dir):
        parser.error(f'Backend not found at {args.backend_dir}!')

    # preprocess circuit list
    
    circuits = []
    for circuit in args.circuits:
        circuits += fnmatch.filter(available, circuit)

    for circuit in circuits:

        if args.just_cpp:
            if not (os.path.exists(os.path.join(output_dir, circuit)) and os.path.exists(os.path.join(output_dir, circuit, 'scal')) and os.path.exists(os.path.join(output_dir, circuit, 'vec'))):
                parser.error(f'No precompiled circuit found for `{circuit}`')
            print(f'Using precompiled circuit for `{circuit}`')
            scalars[circuit] = open(os.path.join(output_dir, circuit, 'scal')).readlines()
            vectors[circuit] = open(os.path.join(output_dir, circuit, 'vec')).readlines()
        else:
            if os.path.exists(os.path.join(output_dir, circuit)):
                print(f'Warning: overwriting {circuit}')
            else:
                os.mkdir(os.path.join(output_dir, circuit))
            print(f'Building {args.coyote_file}/{circuit}...')
            start = time()
            scalar = coyote.instantiate(circuit)
            vector = coyote.vectorize()
            print(f'Finished in {time() - start:.2f}s')

            scalars[circuit] = scalar
            vectors[circuit] = list(map(str, vector))

            open(os.path.join(output_dir, circuit, 'scal'), 'w').write('\n'.join(scalar))
            open(os.path.join(output_dir, circuit, 'vec'), 'w').write('\n'.join(map(str, vector)))

    if not args.no_cpp:
        for circuit in circuits:
            if os.path.exists(os.path.join(args.backend_dir, 'coyote_out', circuit)):
                print(f'Warning: overwriting C++ for {circuit}')
            else:
                os.makedirs(os.path.join(args.backend_dir, 'coyote_out', circuit))

            scalar_cpp = compile_scalar(scalars[circuit])
            vector_cpp = compile_vector(vectors[circuit])

            open(os.path.join(args.backend_dir, 'coyote_out', circuit, 'scalar.cpp'), 'w').write(scalar_cpp)
            open(os.path.join(args.backend_dir, 'coyote_out', circuit, 'vector.cpp'), 'w').write(vector_cpp)


if __name__ == '__main__':
    main()