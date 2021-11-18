cmake_minimum_required(VERSION 3.19.0)
project(CoyoteBFVBackend VERSION 0.1.0)

include(CTest)
include(CMakeFindDependencyMacro)

set(CMAKE_BUILD_TYPE Debug)

enable_testing()

add_executable(CoyoteBFVBackend main.cpp util.cpp
	tree50,50-6_1/scalar.cpp
	tree50,50-6_1/vector.cpp
)

find_package(SEAL 3.7 REQUIRED)
target_link_libraries(CoyoteBFVBackend SEAL::seal)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
