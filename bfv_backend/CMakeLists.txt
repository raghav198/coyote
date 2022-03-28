cmake_minimum_required(VERSION 3.19.0)
project(CoyoteBFVBackend VERSION 0.1.0)

include(CTest)
include(CMakeFindDependencyMacro)

set(CMAKE_BUILD_TYPE Release)
set(COYOTE_PROGRAM mat_mult2x2)

enable_testing()

add_executable(${COYOTE_PROGRAM} main.cpp util.cpp
			${COYOTE_PROGRAM}/scalar.cpp
			${COYOTE_PROGRAM}/vector.cpp
)

find_package(SEAL 3.7 REQUIRED)
target_link_libraries(${COYOTE_PROGRAM} SEAL::seal_shared)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)
