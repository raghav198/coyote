cmake_minimum_required(VERSION 3.0.0)
project(CoyoteBFVBackend VERSION 0.1.0)

include(CTest)
enable_testing()

add_executable(CoyoteBFVBackend main.cpp util.cpp
            small_test/scalar.cpp
            small_test/vector.cpp
)

find_package(SEAL 3.6 REQUIRED)
target_link_libraries(CoyoteBFVBackend SEAL::seal)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
