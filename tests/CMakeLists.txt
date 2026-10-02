enable_testing()

# Which solvers were built, and where. Read only by the tests, so
# defined only for them rather than for the whole project.
add_compile_definitions(${SOLVER_COMPILE_DEFINITIONS})

# The generic solver drives a solver's executable rather than the library the
# rest of the suite links, so it has to be found separately. A provisioned
# copy, or one given with --<solver>-dir, keeps it under the solver's root; a
# system-installed one has it on the PATH, which find_program searches after
# the hint. Defined only when found, so that the tests can leave the solver
# out instead of failing; a path set with -D<VARIABLE> is used as given.
function(smt_switch_find_solver_binary enabled package name variable)
  if(NOT ${enabled})
    return()
  endif()
  find_program(${variable} NAMES ${name} HINTS "${${package}_ROOT}/bin")
  if(${variable})
    add_compile_definitions("${variable}=\"${${variable}}\"")
  else()
    message(STATUS "No ${name} executable found, so the generic solver tests skip it")
  endif()
endfunction()

smt_switch_find_solver_binary(BUILD_BITWUZLA Bitwuzla bitwuzla BITWUZLA_BINARY)
smt_switch_find_solver_binary(BUILD_BTOR Boolector boolector BOOLECTOR_BINARY)
smt_switch_find_solver_binary(BUILD_CVC5 cvc5 cvc5 CVC5_BINARY)
smt_switch_find_solver_binary(BUILD_MSAT MathSAT mathsat MATHSAT_BINARY)
smt_switch_find_solver_binary(BUILD_YICES2 Yices2 yices-smt2 YICES2_BINARY)
smt_switch_find_solver_binary(BUILD_Z3 Z3 z3 Z3_BINARY)

option(SYSTEM_GTEST "Should we try to use the system GTest" ON)
if(SYSTEM_GTEST)
  find_package(GTest 1.14 CONFIG)
else()
  set(GTest_FOUND FALSE)
endif()

if(NOT GTest_FOUND)
  include(FetchContent)
  set(INSTALL_GTEST OFF)
  # Give extracted files the time of extraction, so that changing the URL
  # rebuilds GoogleTest. CMake before 3.24 has neither the policy nor the
  # DOWNLOAD_EXTRACT_TIMESTAMP option.
  if(POLICY CMP0135)
    cmake_policy(SET CMP0135 NEW)
  endif()
  FetchContent_Declare(
    googletest
    URL "https://github.com/google/googletest/archive/refs/tags/v1.18.0.tar.gz"
    URL_HASH "SHA256=6e3191c1455468b3fc35a417fb565c1c5071aee1b7e7f85e30cf48a98d37d8b5"
  )
  FetchContent_MakeAvailable(googletest)
endif()

# Static, because a shared library would carry its own copy of a static
# GTest, and the tests would work only while the linker happens to resolve
# their GTest symbols to that copy rather than to a second one.
add_library(exec-utils STATIC "${PROJECT_SOURCE_DIR}/tests/exec_utils.cpp")
target_include_directories(exec-utils PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}")
target_link_libraries(exec-utils PRIVATE GTest::gmock)

# Gives the tests smt-switch and the backends to link. When those are
# static, this is a shared library holding them whole, so that the solvers
# are linked once rather than into every test. Linking the archives instead
# would pull in only what something in the library uses, and each test
# would then need a second copy for the rest. Otherwise it only links them.
get_target_property(_smt_switch_type smt-switch TYPE)
if(_smt_switch_type STREQUAL "STATIC_LIBRARY")
  add_library(test-solvers SHARED $<TARGET_OBJECTS:smt-switch>)
  foreach(_backend IN LISTS SOLVER_BACKEND_LIBS)
    target_sources(test-solvers PRIVATE $<TARGET_OBJECTS:${_backend}>)
  endforeach()
  target_link_libraries(test-solvers PRIVATE ${SOLVER_BACKEND_LIBS} Threads::Threads)
  target_include_directories(
    test-solvers
    PUBLIC $<TARGET_PROPERTY:smt-switch,INTERFACE_INCLUDE_DIRECTORIES>
  )
  target_compile_features(test-solvers PUBLIC cxx_std_17)
else()
  add_library(test-solvers INTERFACE)
  target_link_libraries(test-solvers INTERFACE smt-switch ${SOLVER_BACKEND_LIBS})
endif()

# add solver-specific test directories

if(BUILD_BITWUZLA)
  add_subdirectory(bzla)
endif()

if(BUILD_BTOR)
  add_subdirectory(btor)
endif()

if(BUILD_CVC5)
  add_subdirectory(cvc5)
endif()

if(BUILD_MSAT)
  add_subdirectory(msat)
endif()

if(BUILD_YICES2)
  add_subdirectory(yices2)
endif()

if(BUILD_Z3)
  add_subdirectory(z3)
endif()

if(BUILD_BTOR AND BUILD_CVC5 AND BUILD_MSAT AND BUILD_YICES2)
  add_subdirectory(portfolio)
endif()

# general tests

add_library(available-solvers STATIC "${PROJECT_SOURCE_DIR}/tests/available_solvers.cpp")
target_include_directories(available-solvers PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}")
target_link_libraries(available-solvers PUBLIC test-solvers)

macro(switch_add_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/${name}.cpp")
  target_link_libraries(${name} PRIVATE available-solvers)
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

switch_add_test(test-array)
switch_add_test(test-bv)
switch_add_test(test-disjointset)
switch_add_test(test-dt)
switch_add_test(test-generic-solver)
switch_add_test(test-generic-sort)
switch_add_test(test-generic-term)
switch_add_test(test-int)
switch_add_test(test-itp)
switch_add_test(test-logging-solver)
switch_add_test(test-sorting-network)
switch_add_test(test-str)
switch_add_test(test-term-translation)
switch_add_test(test-time-limit)
switch_add_test(test-unsat-core)
switch_add_test(test-unsat-core-reducer)
switch_add_test(test-variadic-ops)

if(SMTLIB_READER)
  switch_add_test(test-smtlib-reader)
  target_compile_definitions(
    test-smtlib-reader
    PRIVATE SMTLIB_TEST_RESOURCE_DIR=${CMAKE_CURRENT_SOURCE_DIR}/smt2
  )
endif()

add_subdirectory(unit)
