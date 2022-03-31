cmake_minimum_required(VERSION 3.19.0)
project(CoyoteBFVBackend VERSION 0.1.0)

list(APPEND BENCHMARKS 
# add all the benchmarks you want to build here, one per line
	decision_tree
	distances_5x5_fully
	distances_4x4_fully
	distances_3x3_fully
	matmul_2x2_fully
	matmul_3x3_fully
	conv_4x2_fully
	conv_5x3_fully
	dot_product_3x3_fully
	dot_product_6x6_fully
	dot_product_10x10_fully
	decision_tree_packed_fully
	distances_5x5_partially
	distances_4x4_partially
	distances_3x3_partially
	matmul_2x2_partially
	matmul_3x3_partially
	conv_4x2_partially
	conv_5x3_partially
	dot_product_3x3_partially
	dot_product_6x6_partially
	dot_product_10x10_partially
	decision_tree_packed_partially
	distances_5x5_un
	distances_4x4_un
	distances_3x3_un
	matmul_2x2_un
	matmul_3x3_un
	conv_4x2_un
	conv_5x3_un
	dot_product_3x3_un
	dot_product_6x6_un
	dot_product_10x10_un
	decision_tree_packed_un)

include(CTest)
include(CMakeFindDependencyMacro)

set(CMAKE_BUILD_TYPE Release)

enable_testing()
foreach(BENCHMARK ${BENCHMARKS})
add_executable(${BENCHMARK} main.cpp util.cpp
			${BENCHMARK}/scalar.cpp
			${BENCHMARK}/vector.cpp
)
set(CMAKE_CXX_FLAGS "-DBENCHMARK_NAME=${BENCHMARK}")
find_package(SEAL 3.7 REQUIRED)
target_link_libraries(${BENCHMARK} SEAL::seal_shared)
endforeach(BENCHMARK)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
