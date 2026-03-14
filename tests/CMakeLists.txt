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
  FetchContent_Declare(googletest
    GIT_REPOSITORY https://github.com/google/googletest.git
    GIT_TAG v1.17.0)
  FetchContent_MakeAvailable(googletest)
endif()

add_library(test-deps SHARED
  "${PROJECT_SOURCE_DIR}/tests/available_solvers.cpp"
  "${PROJECT_SOURCE_DIR}/tests/test-utils.cpp"
)
target_include_directories(test-deps PUBLIC "${PROJECT_SOURCE_DIR}/tests/")
target_link_libraries(test-deps PUBLIC smt-switch)
target_link_libraries(test-deps PRIVATE ${SOLVER_BACKEND_LIBS})
target_link_libraries(test-deps PRIVATE GTest::gmock)

# add solver-specific test directories

if(BUILD_BITWUZLA)
  add_subdirectory(bzla)
endif()

if (BUILD_BTOR)
  add_subdirectory(btor)
endif()

if (BUILD_CVC5)
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

macro(switch_add_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/${name}.cpp")
  target_link_libraries(${name} smt-switch)
  target_link_libraries(${name} test-deps)
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
endif()

add_subdirectory(unit)
