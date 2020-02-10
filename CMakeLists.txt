cmake_minimum_required(VERSION 3.1)

project(smt-switch)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

include_directories ("${PROJECT_SOURCE_DIR}/include")

# add to search path for find_package
list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps")

if (NOT SMT_SWITCH_LIB_TYPE)
  set(SMT_SWITCH_LIB_TYPE SHARED)
endif()

add_library(smt-switch "${SMT_SWITCH_LIB_TYPE}"
  "${PROJECT_SOURCE_DIR}/src/ops.cpp"
  "${PROJECT_SOURCE_DIR}/src/result.cpp"
  "${PROJECT_SOURCE_DIR}/src/sort.cpp"
  "${PROJECT_SOURCE_DIR}/src/term.cpp"
  "${PROJECT_SOURCE_DIR}/src/solver.cpp"
  "${PROJECT_SOURCE_DIR}/src/term_translator.cpp")

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

# should we build boolector?
option (BUILD_BTOR
  "Should we build the libraries for boolector" OFF)

if (BUILD_BTOR)
  set(BTOR_HOME "${PROJECT_SOURCE_DIR}/deps/boolector")
  add_subdirectory (btor)
  set (EXTRA_LIBS ${EXTRA_LIBS} smt-switch-btor)

  # testing
  add_subdirectory(tests/btor)
endif (BUILD_BTOR)

# should we build yices2?
option (BUILD_YICES2
  "Should we build the libraries for boolector" OFF)

if (BUILD_YICES2)
  set(YICES2_HOME "${PROJECT_SOURCE_DIR}/deps/yices2")
  add_subdirectory (yices2)
  set (EXTRA_LIBS ${EXTRA_LIBS} smt-switch-yices2)

  # testing
  add_subdirectory(tests/yices2)
endif (BUILD_YICES2)


# should we build cvc4?
option (BUILD_CVC4
  "Should we build the libraries for cvc4" OFF)

if (BUILD_CVC4)
  set(CVC4_HOME "${PROJECT_SOURCE_DIR}/deps/CVC4")
  add_subdirectory (cvc4)
  set (EXTRA_LIBS ${EXTRA_LIBS} smt-switch-cvc4)

  # testing
  add_subdirectory(tests/cvc4)
endif (BUILD_CVC4)

# should we build msat?
option (BUILD_MSAT
  "Should we build the libraries for mathsat" OFF)

if (BUILD_MSAT)
  set(MSAT_HOME "${PROJECT_SOURCE_DIR}/deps/mathsat")
  add_subdirectory (msat)
  set (EXTRA_LIBS ${EXTRA_LIBS} smt-switch-msat)

  # testing
  add_subdirectory(tests/msat)
endif()

# install smt-switch
install(TARGETS smt-switch DESTINATION lib)

# install public headers
install(DIRECTORY "${PROJECT_SOURCE_DIR}/include/"
        DESTINATION include/smt-switch
        FILES_MATCHING PATTERN "*.h")

# uninstall target
# copied from https://gitlab.kitware.com/cmake/community/wikis/FAQ#can-i-do-make-uninstall-with-cmake
if(NOT TARGET uninstall)
    configure_file(
        "${CMAKE_CURRENT_SOURCE_DIR}/cmake_uninstall.cmake.in"
        "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
        IMMEDIATE @ONLY)

    add_custom_target(uninstall
        COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake)
endif()
