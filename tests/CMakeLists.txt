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

add_library(available-solvers "${SMT_SWITCH_LIB_TYPE}"
  "${PROJECT_SOURCE_DIR}/tests/available_solvers.cpp")

target_include_directories(available-solvers PUBLIC "${PROJECT_SOURCE_DIR}/tests/")
target_link_libraries(available-solvers smt-switch ${SOLVER_BACKEND_LIBS})

add_executable(unit-termiter "${PROJECT_SOURCE_DIR}/tests/unit/unit-termiter.cpp")
target_link_libraries(unit-termiter gtest_main)
target_link_libraries(unit-termiter available-solvers)
add_test(NAME unit-termiter_test COMMAND unit-termiter)

add_executable(unit-printing "${PROJECT_SOURCE_DIR}/tests/unit/unit-printing.cpp")
target_link_libraries(unit-printing gtest_main)
target_link_libraries(unit-printing available-solvers)
add_test(NAME unit-printing_test COMMAND unit-printing)

add_executable(unit-op "${PROJECT_SOURCE_DIR}/tests/unit/unit-op.cpp")
target_link_libraries(unit-op gtest_main)
target_link_libraries(unit-op available-solvers)
add_test(NAME unit-op_test COMMAND unit-op)

add_executable(unit-solving-interface "${PROJECT_SOURCE_DIR}/tests/unit/unit-solving-interface.cpp")
target_link_libraries(unit-solving-interface gtest_main)
target_link_libraries(unit-solving-interface available-solvers)
add_test(NAME unit-solving-interface_test COMMAND unit-solving-interface)

add_executable(test_itp "${PROJECT_SOURCE_DIR}/tests/test_itp.cpp")
target_link_libraries(test_itp gtest_main)
target_link_libraries(test_itp available-solvers)
add_test(NAME test_itp_test COMMAND test_itp)

add_executable(test-int "${PROJECT_SOURCE_DIR}/tests/test-int.cpp")
target_link_libraries(test-int gtest_main)
target_link_libraries(test-int available-solvers)
add_test(NAME test-int_test COMMAND test-int)

add_executable(test-unsat-core "${PROJECT_SOURCE_DIR}/tests/test-unsat-core.cpp")
target_link_libraries(test-unsat-core gtest_main)
target_link_libraries(test-unsat-core available-solvers)
add_test(NAME test-unsat-core_test COMMAND test-unsat-core)

add_executable(unit-transfer "${PROJECT_SOURCE_DIR}/tests/unit/unit-transfer.cpp")
target_link_libraries(unit-transfer gtest_main)
target_link_libraries(unit-transfer available-solvers)
add_test(NAME unit-transfer_test COMMAND unit-transfer)

add_executable(unit-arrays "${PROJECT_SOURCE_DIR}/tests/unit/unit-arrays.cpp")
target_link_libraries(unit-arrays gtest_main)
target_link_libraries(unit-arrays available-solvers)
add_test(NAME unit-arrays_test COMMAND unit-arrays)
