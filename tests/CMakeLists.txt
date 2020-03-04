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

add_library(available-solvers "${SMT_SWITCH_LIB_TYPE}"
  "${PROJECT_SOURCE_DIR}/tests/available_solvers.cpp")

target_include_directories(available-solvers PUBLIC "${PROJECT_SOURCE_DIR}/tests/")
target_link_libraries(available-solvers smt-switch ${SOLVER_BACKEND_LIBS})

add_executable(unit-termiter "${PROJECT_SOURCE_DIR}/tests/unit/unit-termiter.cpp")
target_link_libraries(unit-termiter gtest_main)
target_link_libraries(unit-termiter available-solvers)
add_test(NAME unit-termiter_test COMMAND unit-termiter)

add_executable(unit-op "${PROJECT_SOURCE_DIR}/tests/unit/unit-op.cpp")
target_link_libraries(unit-op gtest_main)
target_link_libraries(unit-op available-solvers)
add_test(NAME unit-op_test COMMAND unit-op)

add_executable(test-int "${PROJECT_SOURCE_DIR}/tests/test-int.cpp")
target_link_libraries(test-int gtest_main)
target_link_libraries(test-int available-solvers)
add_test(NAME test-int_test COMMAND test-int)
