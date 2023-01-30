import argparse
import glob
import os
import shutil
import subprocess
import sys

def ensure_exists(dirname):
    os.makedirs(dirname, exist_ok=True)

parser = argparse.ArgumentParser()
parser.add_argument('-r', '--runs', type=int, default=50)
parser.add_argument('-i', '--iters', type=int, default=50)

args = parser.parse_args()

benchmarks = glob.glob('*', root_dir='bfv_backend/coyote_out')
subprocess.Popen(['cmake', '..', f'-DRUNS={args.runs}', f'-DITERATIONS={args.iters}'], cwd='bfv_backend/build', stdout=sys.stdout, stderr=sys.stderr).wait()
subprocess.Popen('make', cwd='bfv_backend/build', stdout=sys.stdout, stderr=sys.stderr).wait()


ensure_exists('bfv_backend/csvs')

for benchmark in benchmarks:
    if not os.path.exists(f'bfv_backend/csvs/{benchmark}.csv'):
        subprocess.Popen(f'../build/{benchmark}', cwd='bfv_backend/csvs', stdout=sys.stdout, stderr=sys.stderr).wait()
    
# TODO: clean these up by benchmark name and size
csv_files = glob.glob('bfv_backend/csvs/*.csv')
for csv in csv_files:
    parts = os.path.splitext(os.path.basename(csv))[0].split('_')
    if parts[0].startswith('tree'):
        r0, r1, depth = parts[1].split('-')
        dirname = f'bfv_backend/csvs/tree/{r0}-{r1}/{depth}/'
        ensure_exists(dirname)
        # print(f'{csv} -> {fname}, {os.path.isfile(csv)}, {os.path.isfile(fname)}')
        shutil.copy(csv, f'{dirname}/{parts[2]}.csv')
        # os.rename(csv, f'{dirname}/{parts[2]}.csv')
        continue
    repl = parts[-1]
    size = parts[-2]
    name = '_'.join(parts[:-2])
    
    ensure_exists(f'bfv_backend/csvs/{name}/{size}')
    shutil.copy(csv, f'bfv_backend/csvs/{name}/{size}/{"_".join(parts)}.csv')
    # os.rename(csv, f'bfv_backend/csvs/{name}/{size}/{"_".join(parts)}.csv')