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

if (BUILD_CVC4)
  add_subdirectory(cvc4)
endif()

if (BUILD_MSAT)
  add_subdirectory(msat)
endif()

if (BUILD_YICES2)
  add_subdirectory(yices2)
endif()

# googletest tests

add_executable(unit-term "${PROJECT_SOURCE_DIR}/tests/unit/unit-term.cpp")
target_link_libraries(unit-term gtest_main)
target_link_libraries(unit-term test-deps)
add_test(NAME unit-term_test COMMAND unit-term)

add_executable(unit-sort "${PROJECT_SOURCE_DIR}/tests/unit/unit-sort.cpp")
target_link_libraries(unit-sort gtest_main)
target_link_libraries(unit-sort test-deps)
add_test(NAME unit-sort_test COMMAND unit-sort)


add_executable(unit-sort-inference "${PROJECT_SOURCE_DIR}/tests/unit/unit-sort-inference.cpp")
target_link_libraries(unit-sort-inference gtest_main)
target_link_libraries(unit-sort-inference test-deps)
add_test(NAME unit-sort-inference_test COMMAND unit-sort-inference)

add_executable(unit-solver-enums "${PROJECT_SOURCE_DIR}/tests/unit/unit-solver-enums.cpp")
target_link_libraries(unit-solver-enums gtest_main)
target_link_libraries(unit-solver-enums test-deps)
add_test(NAME unit-solver-enums_test COMMAND unit-solver-enums)

add_executable(unit-termiter "${PROJECT_SOURCE_DIR}/tests/unit/unit-termiter.cpp")
target_link_libraries(unit-termiter gtest_main)
target_link_libraries(unit-termiter test-deps)
add_test(NAME unit-termiter_test COMMAND unit-termiter)

add_executable(unit-walker "${PROJECT_SOURCE_DIR}/tests/unit/unit-walker.cpp")
target_link_libraries(unit-walker gtest_main)
target_link_libraries(unit-walker test-deps)
add_test(NAME unit-walker_test COMMAND unit-walker)

add_executable(unit-printing "${PROJECT_SOURCE_DIR}/tests/unit/unit-printing.cpp")
target_link_libraries(unit-printing gtest_main)
target_link_libraries(unit-printing test-deps)
add_test(NAME unit-printing_test COMMAND unit-printing)

add_executable(unit-op "${PROJECT_SOURCE_DIR}/tests/unit/unit-op.cpp")
target_link_libraries(unit-op gtest_main)
target_link_libraries(unit-op test-deps)
add_test(NAME unit-op_test COMMAND unit-op)

add_executable(unit-util "${PROJECT_SOURCE_DIR}/tests/unit/unit-util.cpp")
target_link_libraries(unit-util gtest_main)
target_link_libraries(unit-util test-deps)
add_test(NAME unit-util_test COMMAND unit-util)

add_executable(unit-term-hashtable "${PROJECT_SOURCE_DIR}/tests/unit/unit-term-hashtable.cpp")
target_link_libraries(unit-term-hashtable gtest_main)
target_link_libraries(unit-term-hashtable test-deps)
add_test(NAME unit-term-hashtable_test COMMAND unit-term-hashtable)

add_executable(unit-solving-interface "${PROJECT_SOURCE_DIR}/tests/unit/unit-solving-interface.cpp")
target_link_libraries(unit-solving-interface gtest_main)
target_link_libraries(unit-solving-interface test-deps)
add_test(NAME unit-solving-interface_test COMMAND unit-solving-interface)

add_executable(unit-quantifiers "${PROJECT_SOURCE_DIR}/tests/unit/unit-quantifiers.cpp")
target_link_libraries(unit-quantifiers gtest_main)
target_link_libraries(unit-quantifiers test-deps)
add_test(NAME unit-quantifiers_test COMMAND unit-quantifiers)

add_executable(test_itp "${PROJECT_SOURCE_DIR}/tests/test_itp.cpp")
target_link_libraries(test_itp gtest_main)
target_link_libraries(test_itp test-deps)
add_test(NAME test_itp_test COMMAND test_itp)

add_executable(test-int "${PROJECT_SOURCE_DIR}/tests/test-int.cpp")
target_link_libraries(test-int gtest_main)
target_link_libraries(test-int test-deps)
add_test(NAME test-int_test COMMAND test-int)

add_executable(test-dt "${PROJECT_SOURCE_DIR}/tests/test-dt.cpp")
target_link_libraries(test-dt gtest_main)
target_link_libraries(test-dt test-deps)
add_test(NAME test-dt_test COMMAND test-dt)

add_executable(test-array "${PROJECT_SOURCE_DIR}/tests/test-array.cpp")
target_link_libraries(test-array gtest_main)
target_link_libraries(test-array test-deps)
add_test(NAME test-array_test COMMAND test-array)

add_executable(test_logging_solver "${PROJECT_SOURCE_DIR}/tests/test-logging-solver.cpp")
target_link_libraries(test_logging_solver gtest_main)
target_link_libraries(test_logging_solver test-deps)
add_test(NAME test_logging_solver_test COMMAND test_logging_solver)

add_executable(test_generic_term "${PROJECT_SOURCE_DIR}/tests/test-generic-term.cpp")
target_link_libraries(test_generic_term gtest_main)
target_link_libraries(test_generic_term test-deps)
add_test(NAME test_generic_term_test COMMAND test_generic_term)

add_executable(test_generic_sort "${PROJECT_SOURCE_DIR}/tests/test-generic-sort.cpp")
target_link_libraries(test_generic_sort gtest_main)
target_link_libraries(test_generic_sort test-deps)
add_test(NAME test_generic_sort_test COMMAND test_generic_sort)

add_executable(test_portfolio_solver "${PROJECT_SOURCE_DIR}/tests/test-portfolio-solver.cpp")
target_link_libraries(test_portfolio_solver gtest_main)
target_link_libraries(test_portfolio_solver test-deps)
add_test(NAME test_portfolio_solver_test COMMAND test_portfolio_solver)

add_executable(test_generic_solver "${PROJECT_SOURCE_DIR}/tests/test-generic-solver.cpp")
target_link_libraries(test_generic_solver gtest_main)
target_link_libraries(test_generic_solver test-deps)
add_test(NAME test_generic_solver_test COMMAND test_generic_solver)

add_executable(test-term-translation "${PROJECT_SOURCE_DIR}/tests/test-term-translation.cpp")
target_link_libraries(test-term-translation gtest_main)
target_link_libraries(test-term-translation test-deps)
add_test(NAME test-term-translation_test COMMAND test-term-translation)

add_executable(test-unsat-core "${PROJECT_SOURCE_DIR}/tests/test-unsat-core.cpp")
target_link_libraries(test-unsat-core gtest_main)
target_link_libraries(test-unsat-core test-deps)
add_test(NAME test-unsat-core_test COMMAND test-unsat-core)

add_executable(test-unsat-core-reducer "${PROJECT_SOURCE_DIR}/tests/test-unsat-core-reducer.cpp")
target_link_libraries(test-unsat-core-reducer gtest_main)
target_link_libraries(test-unsat-core-reducer test-deps)
add_test(NAME test-unsat-core-reducer_test COMMAND test-unsat-core-reducer)

add_executable(unit-transfer "${PROJECT_SOURCE_DIR}/tests/unit/unit-transfer.cpp")
target_link_libraries(unit-transfer gtest_main)
target_link_libraries(unit-transfer test-deps)
add_test(NAME unit-transfer_test COMMAND unit-transfer)

add_executable(unit-arrays "${PROJECT_SOURCE_DIR}/tests/unit/unit-arrays.cpp")
target_link_libraries(unit-arrays gtest_main)
target_link_libraries(unit-arrays test-deps)
add_test(NAME unit-arrays_test COMMAND unit-arrays)

add_executable(unit-substitute "${PROJECT_SOURCE_DIR}/tests/unit/unit-substitute.cpp")
target_link_libraries(unit-substitute gtest_main)
target_link_libraries(unit-substitute test-deps)
add_test(NAME unit-substitute_test COMMAND unit-substitute)

add_executable(unit-term-id "${PROJECT_SOURCE_DIR}/tests/unit/unit-term-id.cpp")
target_link_libraries(unit-term-id gtest_main)
target_link_libraries(unit-term-id test-deps)
add_test(NAME unit-term-id_test COMMAND unit-term-id)

add_executable(unit-reset-assertions "${PROJECT_SOURCE_DIR}/tests/unit/unit-reset-assertions.cpp")
target_link_libraries(unit-reset-assertions gtest_main)
target_link_libraries(unit-reset-assertions test-deps)
add_test(NAME unit-reset-assertions_test COMMAND unit-reset-assertions)

add_executable(test-disjointset "${PROJECT_SOURCE_DIR}/tests/test-disjointset.cpp")
target_link_libraries(test-disjointset gtest_main)
target_link_libraries(test-disjointset test-deps)
add_test(NAME test-disjointset_test COMMAND test-disjointset)

