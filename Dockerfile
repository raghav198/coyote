FROM ubuntu

WORKDIR /home/artifact

# install dependencies first
RUN apt-get update && apt-get -y install git python3 python3-pip clang cmake
RUN python3 -m pip install networkx z3-solver
RUN python3 -m pip install matplotlib numpy
RUN apt-get -y install vim

# install Microsoft SEAL
RUN git clone --branch 3.7.1 https://github.com/microsoft/SEAL.git
RUN cd SEAL && cmake -S . -B build && cmake --build build && cmake --install build

# download the compiler
COPY coyote/__init__.py \
    coyote/coyote_ast.py \
    coyote/disjoint_set.py \
    coyote/synthesize_schedule.py \
    coyote/codegen.py \
    coyote/vectorize_circuit.py \
    coyote/

COPY artifact_benchmarks.py benchmarks.py
COPY coyote_compile.py coyote_compile.py
COPY compile_to_bfv.py compile_to_bfv.py
COPY numberTreeGenerator.py numberTreeGenerator.py
COPY artifact_utils/build_and_run_all.py build_and_run_all.py
COPY artifact_utils/figures.py figures.py
COPY artifact_utils/compile_benchmarks.py compile_benchmarks.py
COPY artifact_utils/polynomial_benchmarks.py polynomial_benchmarks.py

# download the backend
COPY bfv_backend/*.cpp bfv_backend/*.hpp bfv_backend/CMakeLists.txt bfv_backend/
RUN mkdir bfv_backend/build
