cmake_minimum_required(VERSION 3.19.0)
project(CoyoteBFVBackend VERSION 0.1.0)

# list(APPEND BENCHMARKS 
# 	# add all the benchmarks you want to build here, one per line
# 	sort_3
# 	max_5
# 	distances_5x5_fully
# 	distances_4x4_fully
# 	distances_3x3_fully
# 	matmul_2x2_fully
# 	matmul_3x3_fully
# 	conv_4x2_fully
# 	conv_5x3_fully
# 	dot_product_3x3_fully
# 	dot_product_6x6_fully
# 	dot_product_10x10_fully
# 	sort_3_packed_fully
# 	max_5_packed_fully
# 	distances_5x5_partially
# 	distances_4x4_partially
# 	distances_3x3_partially
# 	matmul_2x2_partially
# 	matmul_3x3_partially
# 	conv_4x2_partially
# 	conv_5x3_partially
# 	dot_product_3x3_partially
# 	dot_product_6x6_partially
# 	dot_product_10x10_partially
# 	sort_3_packed_partially
# 	max_5_packed_partially
# 	distances_5x5_un
# 	distances_4x4_un
# 	distances_3x3_un
# 	matmul_2x2_un
# 	matmul_3x3_un
# 	conv_4x2_un
# 	conv_5x3_un
# 	dot_product_3x3_un
# 	dot_product_6x6_un
# 	dot_product_10x10_un
# 	sort_3_packed_un
# 	max_5_packed_un
# 	matmul_3x3_case1
# 	matmul_3x3_case2
# 	matmul_3x3_case3
# 	matmul_3x3_case4
# 	matmul_3x3_case5
# )


file(GLOB BENCHMARKS RELATIVE ${CMAKE_CURRENT_SOURCE_DIR}/coyote_out coyote_out/*)

include(CTest)
include(CMakeFindDependencyMacro)

set(CMAKE_BUILD_TYPE Release)

if(NOT RUNS)
	set(RUNS 50)
endif()

if (NOT ITERATIONS)
	set(ITERATIONS 50)
endif()

enable_testing()
foreach(BENCHMARK ${BENCHMARKS})
message("Configuring benchmark ${BENCHMARK}...")
add_executable(${BENCHMARK} main.cpp util.cpp
			coyote_out/${BENCHMARK}/scalar.cpp
			coyote_out/${BENCHMARK}/vector.cpp
)
target_include_directories(${BENCHMARK} PRIVATE ${CMAKE_CURRENT_SOURCE_DIR})
set_target_properties(${BENCHMARK} PROPERTIES COMPILE_FLAGS "-DBENCHMARK_NAME=${BENCHMARK} -DRUNS=${RUNS} -DITERATIONS=${ITERATIONS}")
message("Compile flags: -DBENCHMARK_NAME=${BENCHMARK} -DRUNS=${RUNS} -DITERATIONS=${ITERATIONS}")
find_package(SEAL 3.7 REQUIRED)
target_link_libraries(${BENCHMARK} SEAL::seal)
endforeach(BENCHMARK)