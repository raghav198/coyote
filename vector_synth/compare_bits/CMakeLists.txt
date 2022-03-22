cmake_minimum_required(VERSION 3.19.0)
project(cmp_bits_test VERSION 1.0.0)

include(CMakeFindDependencyMacro)

set(CMAKE_BUILD_TYPE Release)

add_executable(cmp_bits compare_bits.cpp ../bfv_backend/util.cpp)

find_package(SEAL 3.7 REQUIRED)
target_link_libraries(cmp_bits SEAL::seal_shared)
