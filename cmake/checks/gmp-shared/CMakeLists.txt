# Probed by the GMP check in the top level CMakeLists.txt, through
# try_compile's project signature: CMAKE_TRY_COMPILE_TARGET_TYPE offers only
# EXECUTABLE and STATIC_LIBRARY, and the question here is whether GMP can go
# into a shared library at all.

cmake_minimum_required(VERSION 3.14)
project(gmp-shared CXX)

list(APPEND CMAKE_MODULE_PATH "${GMP_CHECK_MODULE_PATH}")
find_package(GMP REQUIRED COMPONENTS ${GMP_CHECK_COMPONENTS})

add_library(gmp-shared SHARED use_gmp.cpp)
target_link_libraries(gmp-shared PRIVATE GMP::${GMP_CHECK_TOP_COMPONENT})
