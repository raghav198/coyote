# Coyote Artifact
## Contents
TODO: insert ToC
## Introduction
This Docker image contains everything necessary to replicate the results of the paper **Coyote: A Compiler for Vectorizing Encrypted Arithmetic Circuits**.
This includes:
* An implementation of the compiler described in the paper (under `coyote/`)
* A backend test harness for profiling the vectorized code Coyote generates (under `bfv_backend/`)
* Implementations of all the benchmarks used in the evaluation (in `benchmarks.py` and `polynomial_benchmarks.py`)
* Various scripts necessary to automate the process of compiling, running, and collecting data from the benchmarks.

## Requirements
### Software
* The `coyote` compiler is implemented in [Python 3.10](https://www.python.org/), and uses the [networkx](https://pypi.org/project/networkx/) and [z3](https://pypi.org/project/z3-solver/) modules for its analysis
* The test harness backend is written in C++ and uses version 3.7 of the [Microsoft SEAL](https://github.com/microsoft/SEAL.git) library for its FHE implementation
* The test harness uses [cmake](https://cmake.org/) for its build system
### Hardware
No specialized hardware is required to use Coyote, beyond whatever may be necessary to efficiently run z3 and SEAL.

## Usage
### Writing a Coyote program
Coyote is a DSL embedded in Python, so Coyote programs are just Python functions.
To tag a function as a circuit for Coyote to compile, first get an instance of the Coyote compiler:
```
from coyote import *
coyote = coyote_compiler()
```
Next, use the compiler to annotate your function with input types:
```
@coyote.define_circuit(A=matrix(3, 3), B=matrix(3, 3))
def matrix_multiply(A, B):
    ...
```
For a full discussion of the available types and their compile-time semantics, see the paper.

Finally, use the build script `coyote_compile.py` to invoke the Coyote compiler on the Python file in which this code is saved:
```
python3 coyote_compile.py benchmarks.py -c matrix_multiply
```

### Invoking the compiler
The Coyote compiler can be invoked from the command line via `coyote_compile.py`.
The example invocation above does the following:
1. It parses `benchmarks.py` and loads a list of all circuits defined in that file
2. It uses Coyote to compile/vectorize the spcified `matrix_multiply` circuit
3. It creates a directory called `matrix_multiply` and saves intermediate scalar and vector code into that directory
4. It lowers the intermediate code into C++ and then creates a directory in `bfv_backend/coyote_cout/matrix_multiply/` and saves the generated C++ there.

The script expects the name of a Python file that defines one or more circuits (as described above), and then takes a number of command-line parameters:
* `-l`, `--list`: Lists all the circuits defined in the file and exit, does not actually compile anything
* `-c`, `--circuits`: Load the specified circuits from the file and compile them into C++
* `-o`, ``-output-dir`: Specify the directory into which to place the generated intermediate code (defaults to the directory from which `coyote_compile.py` is invoked)
* `--backend-dir`: Specify the directory containing the test harness backend (defaults to `bfv_backend/`)
* `--no-cpp`: Stops after generated the intermediate code and doesn't generate C++
* `--just-cpp`: Uses pregenerated intermediate code to generate C++ instead of recompiling the circuit; this fails if it can't find the intermediate code under `[output-dir]/[circuit-name]/`

### Running the test harness
The backend test harness comes with a CMake file that automatically builds binaries for everything under `coyote_out`.
The generated binaries perform a number of `runs`, where each run consists of executing the scalar and vectorized circuits on random encrypted inputs for a number of `iterations` and then outputting the total time each version (scalar and vector) took to encrypt, as well as run.
All these outputs are then saved into a csv file with the same name as the circuit (e.g. running the binary generated from the example above would create a file called `matrix_multiply.csv`).

The number of runs and iterations default to 50 each (as these are the values used in the paper), but are configurable via cmake.
An example invocation that uses 10 runs with 10 iterations each is as follows:
```
cd bfv_backend && mkdir build && cd build && cmake .. -DRUNS=10 -DITERATIONS=10 && make
```

## Using the Artifact
The provided Dockerfile automatically builds and installs all dependencies of Coyote.
To build and run the Docker image, run the following commands from the directory containing the Dockerfile:
```
docker build -t coyote .
docker run -it coyote bash
```
In addition to the compiler and the runtime, the image also conists of various scripts to automatically run the benchmarks from the paper and generate the associated figures.
These are:
* `compile_benchmarks.py`: Automatically invokes the build script on a set of circuits defined in `benchmarks.py`. There are several presets available, `small`, `medium`, and `large`, representing the size of the circuits (and correspondingly the expected compile time).
* `polynomial_benchmarks.py`: Generates and compiles the random tree benchmarks used in Section 6.5 of the paper. 
* `build_and_run_all.py`: Builds binaries from all generated C++ code, invokes them one at a time, and organizes the resulting CSV files.
* `figures.py`: Reads the CSV files and generates the figures from the paper.

### Demo
Lets start by building all the `small` benchmarks (all replication sorts for `conv.4.2`, `mm.2`, `dot.3`, `dot.6`, and `dot.10`, as well as the ungrouped `sort[3]`):
```
python3 compile_benchmarks.py --preset small
```
(This took about 10 minutes on my machine)

Lets also build some of the polynomial trees; in particular, we'll build three of the depth 5 trees in each of the three regimes:
```
python3 polynomial_benchmarks.py -d 5 -r "100-100" "100-50" "50-50" -i 2
```
(This took about 10 minutes on my machine).

We can see, for example, some of the generated vector C++ code:
```
cat bfv_backend/coyote_out/sort_3/vector.cpp
```

We can also build the data layout case study from Section 6.7 of the paper, although note that these circuits are considerably larger, so compiling them will take some time:

```
python3 compile_benchmarks.py --preset layout
```

Now, we need to compile all the C++ code and collect data.
Although we used 50 runs and 50 iterations in the paper, lets only use 10 of each to make this go faster:
```
python3 build_and_run_all.py --runs 10 --iters 10
```
You should see some CMake output followed by the encryption and run times for both scalar and vector versions of each circuit.
Note that this script will not re-run benchmarks that already have corresponding CSV files in `bfv_backend/csvs/`.

Once this is finished running, we can look at one of the generated CSV files:
```
cat bfv_backend/csvs/sort/sort_3.csv
```

Now that we've collected all the data for these benchmarks, we can generate the graphs:
```
python3 figures.py
```

This will generate three plots:
`graphs/vector_speedups.png`, `case_study.png`, and `trees.png`.
To view these, either attach to the running Docker container (e.g. using VS Code), or copy the files to your host machine:
```
docker cp $(docker ps -q):/home/artifact/graphs/ .
```