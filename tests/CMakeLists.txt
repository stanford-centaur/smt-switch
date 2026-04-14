enable_testing()

option(SYSTEM_GTEST "Should we try to use the system GTest" ON)
if(SYSTEM_GTEST)
  find_package(GTest 1.14 CONFIG)
else()
  set(GTest_FOUND FALSE)
endif()

if(NOT GTest_FOUND)
  include(FetchContent)
  set(INSTALL_GTEST OFF)
  FetchContent_Declare(
    googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.17.0
  )
  FetchContent_MakeAvailable(googletest)
endif()

add_library(exec-utils SHARED "${PROJECT_SOURCE_DIR}/tests/exec_utils.cpp")
target_include_directories(exec-utils PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}")
target_link_libraries(exec-utils PRIVATE GTest::gmock)

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

add_library(available-solvers SHARED "${PROJECT_SOURCE_DIR}/tests/available_solvers.cpp")
target_include_directories(available-solvers PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}")
target_link_libraries(available-solvers PUBLIC smt-switch)
target_link_libraries(available-solvers PRIVATE ${SOLVER_BACKEND_LIBS})

macro(switch_add_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/${name}.cpp")
  target_link_libraries(${name} available-solvers)
  target_link_libraries(${name} smt-switch)
  target_link_libraries(${name} GTest::gtest_main)
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
