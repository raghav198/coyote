cmake_minimum_required(VERSION 3.19.0)
project(CoyoteBFVBackend VERSION 0.1.0)

list(APPEND BENCHMARKS 
# add all the benchmarks you want to build here, one per line
	tree_100-100-5_1
	tree_100-100-5_2
	tree_100-100-5_3
	tree_100-100-5_4
	tree_100-100-5_5
	tree_100-100-10_1
	tree_100-100-10_2
	tree_100-100-10_3
	tree_100-100-10_4
	tree_100-100-10_5
	tree_100-50-5_1
	tree_100-50-5_2
	tree_100-50-5_3
	tree_100-50-5_4
	tree_100-50-5_5
	tree_100-50-10_1
	tree_100-50-10_2
	tree_100-50-10_3
	tree_100-50-10_4
	tree_100-50-10_5
	tree_50-50-5_1
	tree_50-50-5_2
	tree_50-50-5_3
	tree_50-50-5_4
	tree_50-50-5_5
	tree_50-50-10_1
	tree_50-50-10_2
	tree_50-50-10_3
	tree_50-50-10_4
	tree_50-50-10_5)

include(CTest)
include(CMakeFindDependencyMacro)

set(CMAKE_BUILD_TYPE Release)

enable_testing()
foreach(BENCHMARK ${BENCHMARKS})
add_executable(${BENCHMARK} main.cpp util.cpp
			${BENCHMARK}/scalar.cpp
			${BENCHMARK}/vector.cpp
)
set_target_properties(${BENCHMARK} PROPERTIES COMPILE_FLAGS "-DBENCHMARK_NAME=${BENCHMARK}")
find_package(SEAL 3.7 REQUIRED)
if(TARGET SEAL::seal)
	target_link_libraries(${BENCHMARK} SEAL::seal)
elseif(TARGET SEAL::seal_shared)
	target_link_libraries(${BENCHMARK} SEAL::seal_shared)
endif()
endforeach(BENCHMARK)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
