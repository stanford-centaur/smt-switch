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
  "${PROJECT_SOURCE_DIR}/src/solver.cpp")

# build testing infrastructure
enable_testing()

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


# should we build boolector?
option (BUILD_CVC4
  "Should we build the libraries for boolector" OFF)

if (BUILD_CVC4)
  set(CVC4_HOME "${PROJECT_SOURCE_DIR}/deps/CVC4")
  add_subdirectory (cvc4)
  set (EXTRA_LIBS ${EXTRA_LIBS} smt-switch-cvc4)

  # testing
  add_subdirectory(tests/cvc4)
endif (BUILD_CVC4)

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
