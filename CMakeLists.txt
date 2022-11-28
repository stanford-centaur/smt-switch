cmake_minimum_required(VERSION 3.1)

project(smt-switch)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

set(CMAKE_POSITION_INDEPENDENT_CODE ON)
list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/cmake)

set(INCLUDE_DIRS
  "${PROJECT_SOURCE_DIR}/include")

# add to search path for find_package
list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps")

if (NOT SMT_SWITCH_LIB_TYPE)
  set(SMT_SWITCH_LIB_TYPE SHARED)
endif()

add_definitions(-DSMT_SWITCH_DIR=${PROJECT_SOURCE_DIR})

set (SOURCES "${SMT_SWITCH_LIB_TYPE}"
  "${PROJECT_SOURCE_DIR}/include/smtlib_utils.h"
  "${PROJECT_SOURCE_DIR}/src/datatype.cpp"
  "${PROJECT_SOURCE_DIR}/src/generic_datatype.cpp"
  "${PROJECT_SOURCE_DIR}/src/generic_solver.cpp"
  "${PROJECT_SOURCE_DIR}/src/generic_sort.cpp"
  "${PROJECT_SOURCE_DIR}/src/generic_term.cpp"
  "${PROJECT_SOURCE_DIR}/src/identity_walker.cpp"
  "${PROJECT_SOURCE_DIR}/src/tree_walker.cpp"
  "${PROJECT_SOURCE_DIR}/src/logging_sort.cpp"
  "${PROJECT_SOURCE_DIR}/src/logging_term.cpp"
  "${PROJECT_SOURCE_DIR}/src/logging_solver.cpp"
  "${PROJECT_SOURCE_DIR}/src/ops.cpp"
  "${PROJECT_SOURCE_DIR}/src/printing_solver.cpp"
  "${PROJECT_SOURCE_DIR}/include/smtlib_utils.h"
  "${PROJECT_SOURCE_DIR}/src/portfolio_solver.cpp"
  "${PROJECT_SOURCE_DIR}/src/result.cpp"
  "${PROJECT_SOURCE_DIR}/src/solver.cpp"
  "${PROJECT_SOURCE_DIR}/src/solver_enums.cpp"
  "${PROJECT_SOURCE_DIR}/src/solver_utils.cpp"
  "${PROJECT_SOURCE_DIR}/src/sort_inference.cpp"
  "${PROJECT_SOURCE_DIR}/src/sort.cpp"
  "${PROJECT_SOURCE_DIR}/src/sorting_network.cpp"
  "${PROJECT_SOURCE_DIR}/src/substitution_walker.cpp"
  "${PROJECT_SOURCE_DIR}/src/term.cpp"
  "${PROJECT_SOURCE_DIR}/src/term_hashtable.cpp"
  "${PROJECT_SOURCE_DIR}/src/term_translator.cpp"
  "${PROJECT_SOURCE_DIR}/src/utils.cpp")

if (SMTLIB_READER)
  if (BISON_DIR)
    list(APPEND CMAKE_PREFIX_PATH "${BISON_DIR}")
  else()
    # default location if using contrib/setup-bison.sh
    # will also search global paths
    list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps/bison/bison-install")
  endif()

  if (FLEX_DIR)
    list(APPEND CMAKE_PREFIX_PATH "${FLEX_DIR}")
  else()
    # default location if using contrib/setup-flex.sh
    # will also search global paths
    list(APPEND CMAKE_PREFIX_PATH "${PROJECT_SOURCE_DIR}/deps/flex/flex-install")
  endif()

  find_package(BISON 3.7.0 REQUIRED)
  find_package(FLEX 2.6.4 REQUIRED)

  if (BISON_FOUND)
    get_filename_component(BISON_PARENT_DIR "${BISON_EXECUTABLE}" DIRECTORY)
    message("-- Adding bison lib: ${BISON_PARENT_DIR}/../lib")
    link_directories("${BISON_PARENT_DIR}/../lib/")
  endif()

  BISON_TARGET(SmtLibParser ${PROJECT_SOURCE_DIR}/src/smtlibparser.yy
    ${CMAKE_CURRENT_BINARY_DIR}/smtlibparser.cpp
    DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/smtlibparser.h)

  FLEX_TARGET(SmtLibScanner ${PROJECT_SOURCE_DIR}/src/smtlibscanner.l
    ${CMAKE_CURRENT_BINARY_DIR}/smtlibscanner.cpp)

  ADD_FLEX_BISON_DEPENDENCY(SmtLibScanner SmtLibParser)

  # putting generated header files in build dir
  set(INCLUDE_DIRS "${INCLUDE_DIRS}" "${CMAKE_BINARY_DIR}")

  set(SOURCES "${SOURCES}"
    "${PROJECT_SOURCE_DIR}/src/smtlib_reader.cpp"
    "${BISON_SmtLibParser_OUTPUTS}"
    "${FLEX_SmtLibScanner_OUTPUTS}")
else()
  # if not building with SmtLibReader
  # then exclude the relevant header files from installing
  set(EXCLUDE_HEADERS_INSTALL
    PATTERN "smtlib_reader.h" EXCLUDE
    PATTERN "smtlibparser_maps.h" EXCLUDE)
endif()

include_directories (${INCLUDE_DIRS})

add_library(smt-switch "${SMT_SWITCH_LIB_TYPE}" ${SOURCES})

set(THREADS_PREFER_PTHREAD_FLAG True)
find_package(Threads)
target_link_libraries( smt-switch PRIVATE Threads::Threads)

# Should we build python bindings
option (BUILD_PYTHON_BINDINGS
   "Build Python bindings")
option (USE_PYTHON2
   "Use Python2 for bindings")

# Decide on Python version before setting up googletest
# Otherwise might use wrong version
if (BUILD_PYTHON_BINDINGS)
  # We currently use FindPythonInterp even though it is deprecated since 3.12
  # This is because the scikit-build files still use this version and it will
  # not interact well with the latest Python finding cmake modules
  # https://cmake.org/cmake/help/v3.12/module/FindPython.html
  # in the future, we can switch to FindPython3 once it has become more standard
  # i.e. when the following issue is resolved:
  # https://github.com/scikit-build/scikit-build/issues/506
  find_package(PythonInterp 3.5 REQUIRED)
endif()

if (BUILD_BITWUZLA OR BUILD_CVC5 OR BUILD_MSAT OR BUILD_YICES2 OR BUILD_Z3)
  find_package(GMP REQUIRED)
endif()

# should we build boolector?
option (BUILD_BTOR
  "Should we build the libraries for boolector" OFF)

if (BUILD_BTOR)
  if (NOT DEFINED BTOR_HOME)
    set(BTOR_HOME "${PROJECT_SOURCE_DIR}/deps/boolector")
  endif()
  add_subdirectory (btor)
  set (SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-btor)

  add_definitions(-DBUILD_BTOR)
  add_definitions(-DBTOR_HOME=${BTOR_HOME})
endif (BUILD_BTOR)

# should we build bitwuzla?
option (BUILD_BITWUZLA
  "Should we build the libraries for bitwuzla" OFF)
if (BUILD_BITWUZLA)
  if (NOT DEFINED BITWUZLA_HOME)
    set(BITWUZLA_HOME "${PROJECT_SOURCE_DIR}/deps/bitwuzla")
  endif()
  add_subdirectory (bitwuzla)
  set (SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-bitwuzla)

  add_definitions(-DBUILD_BITWUZLA)
  add_definitions(-DBITWUZLA_HOME=${BITWUZLA_HOME})
endif (BUILD_BITWUZLA)


# should we build cvc5?
option (BUILD_CVC5
  "Should we build the libraries for cvc5" OFF)

if (BUILD_CVC5)
  if (NOT DEFINED CVC5_HOME)
    set(CVC5_HOME "${PROJECT_SOURCE_DIR}/deps/cvc5")
  endif()
  add_subdirectory (cvc5)
  set (SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-cvc5)

  add_definitions(-DBUILD_CVC5)
  add_definitions(-DCVC5_HOME=${CVC5_HOME})
endif (BUILD_CVC5)

# should we build msat?
option (BUILD_MSAT
  "Should we build the libraries for mathsat" OFF)

if (BUILD_MSAT)
  if (NOT DEFINED MSAT_HOME)
    set(MSAT_HOME "${PROJECT_SOURCE_DIR}/deps/mathsat")
  endif()
  add_subdirectory (msat)
  set (SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-msat)

  add_definitions(-DBUILD_MSAT)
  add_definitions(-DMSAT_HOME=${MSAT_HOME})
endif()

# should we build z3?
option (BUILD_Z3
  "Should we build the libraries for z3" OFF)

if (BUILD_Z3)
  set(Z3_HOME "${PROJECT_SOURCE_DIR}/deps/z3")
  add_subdirectory (z3)
  set (SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-z3)

  add_definitions(-DBUILD_Z3)
  add_definitions(-DZ3_HOME=${Z3_HOME})
endif (BUILD_Z3)

# should we build yices2?
option (BUILD_YICES2
  "Should we build the libraries for yices2" OFF)

if (BUILD_YICES2)
  if (NOT DEFINED YICES2_HOME)
    set(YICES2_HOME "${PROJECT_SOURCE_DIR}/deps/yices2")
  endif()
  add_subdirectory (yices2)
  set (SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-yices2)

  add_definitions(-DBUILD_YICES2)
  add_definitions(-DYICES2_HOME=${YICES2_HOME})
endif (BUILD_YICES2)

if (BUILD_PYTHON_BINDINGS)
  add_subdirectory(python)
endif()

# should we build the tests
option (BUILD_TESTS
  "Should we build the test suite" ON)

if (BUILD_TESTS)
  # build testing infrastructure
  enable_testing()

  # Add tests subdirectory
  # The CMakeLists.txt file there sets up googletest
  # and builds all the parametrized tests
  add_subdirectory(tests)
endif()

# install smt-switch
install(TARGETS smt-switch DESTINATION lib)

# install public headers
install(DIRECTORY "${PROJECT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  ${EXCLUDE_HEADERS_INSTALL})

if (SMTLIB_READER)
  install(FILES "${CMAKE_BINARY_DIR}/smtlibparser.h"
    DESTINATION include/smt-switch)

  install(FILES "${CMAKE_BINARY_DIR}/location.hh"
    DESTINATION include/smt-switch)
endif()

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
