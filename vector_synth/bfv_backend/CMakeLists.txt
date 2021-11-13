cmake_minimum_required(VERSION 3.19.0)
project(CoyoteBFVBackend VERSION 0.1.0)

include(CTest)
include(CMakeFindDependencyMacro)

set(CMAKE_BUILD_TYPE Debug)

enable_testing()

add_executable(CoyoteBFVBackend main.cpp util.cpp
            determinant3x3/scalar.cpp
            determinant3x3/vector.cpp
)

find_package(SEAL 3.6 REQUIRED)
target_link_libraries(CoyoteBFVBackend SEAL::seal_shared)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
