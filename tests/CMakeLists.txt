# Set Up Google Tests

# build testing infrastructure
enable_testing()

# Download and unpack googletest at configure time
configure_file(CMakeLists.txt.in googletest-download/CMakeLists.txt)
execute_process(COMMAND ${CMAKE_COMMAND} -G "${CMAKE_GENERATOR}" .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/googletest-download )
if(result)
  message(FATAL_ERROR "CMake step for googletest failed: ${result}")
endif()
execute_process(COMMAND ${CMAKE_COMMAND} --build .
  RESULT_VARIABLE result
  WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/googletest-download )
if(result)
  message(FATAL_ERROR "Build step for googletest failed: ${result}")
endif()

# Add googletest directly to our build. This defines
# the gtest and gtest_main targets.
add_subdirectory(${CMAKE_CURRENT_BINARY_DIR}/googletest-src
                 ${CMAKE_CURRENT_BINARY_DIR}/googletest-build
                 EXCLUDE_FROM_ALL)

add_library(test-deps "${SMT_SWITCH_LIB_TYPE}"
  "${PROJECT_SOURCE_DIR}/tests/available_solvers.cpp"
  "${PROJECT_SOURCE_DIR}/tests/test-utils.cpp"
  )

target_include_directories(test-deps PUBLIC "${PROJECT_SOURCE_DIR}/tests/")
target_link_libraries(test-deps smt-switch ${SOLVER_BACKEND_LIBS})

# add solver-specific test directories
# these do not use googletest
if (BUILD_BTOR)
  add_subdirectory(btor)
endif()

if (BUILD_CVC5)
  add_subdirectory(cvc5)
endif()

if (BUILD_MSAT)
  add_subdirectory(msat)
endif()

if (BUILD_YICES2)
  add_subdirectory(yices2)
endif()

if (${BUILD_YICES2} AND ${BUILD_BTOR} AND ${BUILD_MSAT} AND ${BUILD_CVC5})
  add_subdirectory(portfolio)
endif()

if (BUILD_Z3)
  add_subdirectory(z3)
endif()

# googletest tests

macro(switch_add_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/${name}.cpp")
  target_link_libraries(${name} gtest_main)
  target_link_libraries(${name} test-deps)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

switch_add_test(test-array)
switch_add_test(test-disjointset)
switch_add_test(test-dt)
switch_add_test(test-generic-solver)
switch_add_test(test-generic-sort)
switch_add_test(test-generic-term)
switch_add_test(test-int)
switch_add_test(test-bv)
switch_add_test(test-itp)
switch_add_test(test-logging-solver)
switch_add_test(test-sorting-network)
switch_add_test(test-term-translation)
switch_add_test(test-time-limit)
switch_add_test(test-unsat-core)
switch_add_test(test-unsat-core-reducer)
switch_add_test(test-variadic-ops)

if (SMTLIB_READER)
  switch_add_test(test-smtlib-reader)
endif()

add_subdirectory(unit)
