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


# Define C macros for available_solvers
# used in the parametrized tests so that it knows which
# solvers to run with
if (BUILD_BTOR)
  add_definitions(-DBUILD_BTOR)
endif(BUILD_BTOR)

if (BUILD_CVC4)
  add_definitions(-DBUILD_CVC4)
endif(BUILD_CVC4)

if (BUILD_MSAT)
  add_definitions(-DBUILD_MSAT)
endif(BUILD_MSAT)

if (BUILD_YICES2)
  add_definitions(-DBUILD_YICES2)
endif(BUILD_YICES2)

add_library(test-deps "${SMT_SWITCH_LIB_TYPE}"
  "${PROJECT_SOURCE_DIR}/tests/available_solvers.cpp"
  "${PROJECT_SOURCE_DIR}/tests/test-utils.cpp"
  )

target_include_directories(test-deps PUBLIC "${PROJECT_SOURCE_DIR}/tests/")
target_link_libraries(test-deps smt-switch ${SOLVER_BACKEND_LIBS})

add_executable(unit-termiter "${PROJECT_SOURCE_DIR}/tests/unit/unit-termiter.cpp")
target_link_libraries(unit-termiter gtest_main)
target_link_libraries(unit-termiter test-deps)
add_test(NAME unit-termiter_test COMMAND unit-termiter)

add_executable(unit-printing "${PROJECT_SOURCE_DIR}/tests/unit/unit-printing.cpp")
target_link_libraries(unit-printing gtest_main)
target_link_libraries(unit-printing test-deps)
add_test(NAME unit-printing_test COMMAND unit-printing)

add_executable(unit-op "${PROJECT_SOURCE_DIR}/tests/unit/unit-op.cpp")
target_link_libraries(unit-op gtest_main)
target_link_libraries(unit-op test-deps)
add_test(NAME unit-op_test COMMAND unit-op)

add_executable(unit-term-hashtable "${PROJECT_SOURCE_DIR}/tests/unit/unit-term-hashtable.cpp")
target_link_libraries(unit-term-hashtable gtest_main)
target_link_libraries(unit-term-hashtable test-deps)
add_test(NAME unit-term-hashtable_test COMMAND unit-term-hashtable)

add_executable(unit-solving-interface "${PROJECT_SOURCE_DIR}/tests/unit/unit-solving-interface.cpp")
target_link_libraries(unit-solving-interface gtest_main)
target_link_libraries(unit-solving-interface test-deps)
add_test(NAME unit-solving-interface_test COMMAND unit-solving-interface)

add_executable(test_itp "${PROJECT_SOURCE_DIR}/tests/test_itp.cpp")
target_link_libraries(test_itp gtest_main)
target_link_libraries(test_itp test-deps)
add_test(NAME test_itp_test COMMAND test_itp)

add_executable(test-int "${PROJECT_SOURCE_DIR}/tests/test-int.cpp")
target_link_libraries(test-int gtest_main)
target_link_libraries(test-int test-deps)
add_test(NAME test-int_test COMMAND test-int)

add_executable(test-array "${PROJECT_SOURCE_DIR}/tests/test-array.cpp")
target_link_libraries(test-array gtest_main)
target_link_libraries(test-array test-deps)
add_test(NAME test-array_test COMMAND test-array)

add_executable(test_logging_solver "${PROJECT_SOURCE_DIR}/tests/test-logging-solver.cpp")
target_link_libraries(test_logging_solver gtest_main)
target_link_libraries(test_logging_solver test-deps)
add_test(NAME test_logging_solver_test COMMAND test_logging_solver)

add_executable(test-term-translation "${PROJECT_SOURCE_DIR}/tests/test-term-translation.cpp")
target_link_libraries(test-term-translation gtest_main)
target_link_libraries(test-term-translation test-deps)
add_test(NAME test-term-translation_test COMMAND test-term-translation)
