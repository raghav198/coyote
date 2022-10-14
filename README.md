# Coyote
Coyote is an FHE-based programming language for compiling and vectorizing arithmetic circuits.

## Getting Started
### Installation
To get started using Coyote, simply install the package with `pip`, either by cloning this repository locally and running `pip install /path/to/repository` or by installing directly from GitHub with
`pip install git+https://github.com/raghav198/coyote`.
This will install the `coyote` package, which contains everything you need to write Coyote programs, and will install the `coyotecc` compiler for Coyote. 

To run compiled Coyote programs, you need Microsoft's [SEAL](https://github.com/microsoft/SEAL/) library for Fully Homomorphic Encryption.

### Writing Coyote programs
Coyote is a DSL embedded in Python, and programs are just decorated Python functions.
The example below demonstrates a simple arithmetic circuit defined in Coyote:

```
from coyote import *

coyote = coyote_compiler()

@coyote.define_circuit(a=scalar(), b=scalar())
def sum_squares(a, b):
    return a * a + b * b
```

The decorator `@coyote.define_circuit` registers `sum_squares` as a Coyote circuit, and defines its signature as taking two scalar inputs, `a` and `b`.

Coyote supports three kinds of input datatypes: `scalar()`, `vector(sz)`, and `matrix(rows, cols)`.
Scalars represent single numbers, while vectors and matrices can be thought of as encoding fixed-size arrays of inputs.
Vectors and matrices behave like regular Python lists or lists-of-lists, and can be indexed and looped over as normal.

At compile-time, Coyote instantiates symbolic variables in place of each of the inputs and calls the registered function with these symbolic variables as arguments to produce an arithmetic circuit.
Coyote packs inputs annotated with `vector(sz)` or `matrix(rows, cols)` into ciphertext vectors, and also attempts to pack `scalar()` inputs into vectors as much as possible.

A single file can contain multiple Coyote programs, and can use any Python features as long as no unsupported operations are performed on any ciphertexts (unsupported operations include branching on or comparing two ciphertexts).
In particular, a Coyote program can invoke another Coyote program by simply calling it like a normal function, as shown in the example below:

```
from coyote import *

coyote = coyote_compiler()

@coyote.define_circuit(v1=vector(3), v2=vector(3))
def dot(v1, v2):
    return sum([a * b for a, b in zip(v1, v2)])

@coyote.define_circuit(A=matrix(3, 3), b=vector(3))
def matvec_mul(A, b):
    return [dot(row, b) for row in A]
```

### Compiling Coyote programs
Once your arithmetic circuits are defined, the `coyotecc` compiler can be invoked to compile these into efficient C++.
For each circuit, Coyote first serializes it as a scalar program, and then vectorizes it.
The scalar and vector programs are saved in a textual intermediate representation (IR), and then further lowered to C++ code that links against the [SEAL](https://github.com/microsoft/SEAL/) library. 


The compiler supports the following options:

* `-l, --list`: List the circuits defined in the file without compiling any
* `-c, --circuits`: Specify which set of circuits to compile
* `-o, --output-dir`: Specify where to place the intermediate scalar and vector outputs
* `--backend-dir`: Path to the Coyote backend, determines where the generated C++ gets placed
* `--combine`: Instead of compiling each circuit separately, combine them into one large circuit to compile (takes longer, but opens the opportunity to vectorize across different circuits)
* `--no-cpp`: Stop after compiling to IR and before lowering to C++
* `--just-cpp`: Directly lower precompiled IR to C++.
