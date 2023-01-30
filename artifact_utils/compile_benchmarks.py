import argparse
import os

circuit_presets = {
    'small': ['dot_product_*_*', 'matmul_2x2_*', 'conv_4x2_*', 'sort_3'],
    'medium': ['conv_5x3_*', 'distances_3x3_*', 'sort_3_*'],
    'large': ['distances_4x4_*', 'distances_5x5_*', 'matmul_3x3_*', 'max_5', 'max_5_*'],
    'layouts': ['matmul_3x3_case*']
    # TODO: we can add some more groups here
}

parser = argparse.ArgumentParser()

circuit_group = parser.add_mutually_exclusive_group(required=True)
circuit_group.add_argument('-p', '--preset', choices=list(circuit_presets.keys()))
circuit_group.add_argument('-c', '--circuits', nargs='+')

parser.add_argument('-r', '--repl', choices=['fully', 'partially', 'un', 'all'], default='all')

args = parser.parse_args()
if args.preset:
    circuits = circuit_presets[args.preset]
else:
    circuits = args.circuits
    
if args.repl != 'all':
    circuits = [circuit.replace('*', args.repl) for circuit in circuits]
    
# print(circuits)
cmd = 'python3 coyote_compile.py benchmarks.py -c ' + ' '.join(f'"{circuit}"' for circuit in circuits)
print(cmd)
os.system(cmd)

# subprocess.Popen(['python3', 'coyote_compile.py', 'benchmarks.py', '-c', ' '.join(f'"{circuit}"' for circuit in circuits)], stdout=sys.stdout, stderr=sys.stderr).wait()