cmake_minimum_required(VERSION 3.14)

project(smt-switch)

# The library and its public headers are C++11. Three places raise it, each
# saying so on its own target: the cvc5 and bitwuzla backends, whose solver
# APIs are C++17; tests/, for GoogleTest; and the z3 backend, at C++14.
#
# Pinned rather than merely requested, so that reaching for a newer feature
# fails here instead of compiling against whatever the compiler defaults to.
# The guard leaves -DCMAKE_CXX_STANDARD= able to override it; a plain set()
# shadows the cache entry that creates, and the flag would not change.
if(NOT DEFINED CMAKE_CXX_STANDARD)
  set(CMAKE_CXX_STANDARD 11)
endif()
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)
set(CMAKE_EXPORT_COMPILE_COMMANDS ON)
set(CMAKE_INSTALL_MESSAGE LAZY)
set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Restricted to C++ because btor/ compiles a C file.
add_compile_options(
  "$<$<COMPILE_LANGUAGE:CXX>:-Werror=non-virtual-dtor;-Werror=return-type;-Werror=type-limits>"
)

list(APPEND CMAKE_MODULE_PATH "${PROJECT_SOURCE_DIR}/cmake")

# defines find_python_in_virtualenv()
# a helper to find Python in a virtualenv
find_package(PythonVirtualEnv)

########################### Identify the current version ########################
# Function to parse and validate a version string
# Returns TRUE if valid, FALSE otherwise
function(parse_version_string VERSION_STR)
  # Remove 'v' prefix if present
  if(VERSION_STR MATCHES "^v(.*)")
    set(VERSION_STR ${CMAKE_MATCH_1})
  endif()

  # Check if the version matches semantic versioning format
  if(VERSION_STR MATCHES "^([0-9]+)\\.([0-9]+)\\.([0-9]+)$")
    # Set version components in parent scope
    set(PARSED_VERSION "${CMAKE_MATCH_1}.${CMAKE_MATCH_2}.${CMAKE_MATCH_3}" PARENT_SCOPE)
    return()
  endif()

  # If we get here, version string was invalid
  set(PARSED_VERSION "" PARENT_SCOPE)
endfunction()

# Look up the current version in the VERSION file
file(STRINGS "${PROJECT_SOURCE_DIR}/VERSION" VERSION_LINES)
# Process lines until we find a non-comment line and assume that's the version
foreach(LINE IN LISTS VERSION_LINES)
  # Skip empty lines and comments
  if(LINE AND NOT LINE MATCHES "^[ ]*#")
    parse_version_string("${LINE}")
    if(PARSED_VERSION)
      message(STATUS "Using version from VERSION file: ${PARSED_VERSION}")
      project(${PROJECT_NAME} VERSION ${PARSED_VERSION})
      break()
    endif()
  endif()
endforeach()

if(NOT PARSED_VERSION)
  message(FATAL_ERROR "Could not determine valid version from VERSION file")
endif()

# - PROJECT_VERSION: Full version string
# - PROJECT_VERSION_MAJOR: Major version component
# - PROJECT_VERSION_MINOR: Minor version component
# - PROJECT_VERSION_PATCH: Patch version component
message(STATUS "Project version set to: ${PROJECT_VERSION}")

# Defines SMT_SWITCH_DEPS_DIR, which the roots below are relative to, and
# smt_switch_provision_if_missing(), used further down. Included before the
# roots so that moving the dependency tree moves both together.
include(ProvisionDeps)

# Each dependency installs into its own prefix under SMT_SWITCH_DEPS_DIR.
# Point each package at its own prefix rather than putting them all on
# CMAKE_PREFIX_PATH: a root is scoped to one package, so a dependency can no
# longer shadow an unrelated system library.
#
# These are only defaults. A root passed on the command line wins, and so does
# a package installed where find_package would look anyway.
function(smt_switch_default_root package directory)
  if(NOT DEFINED ${package}_ROOT)
    set(${package}_ROOT "${SMT_SWITCH_DEPS_DIR}/${directory}" PARENT_SCOPE)
  endif()
endfunction()

smt_switch_default_root(BISON bison)
smt_switch_default_root(Bitwuzla bitwuzla)
smt_switch_default_root(Boolector boolector)
smt_switch_default_root(CaDiCaL cadical)
smt_switch_default_root(FLEX flex)
smt_switch_default_root(MathSAT mathsat)
smt_switch_default_root(Yices2 yices2)
smt_switch_default_root(Z3 z3)
smt_switch_default_root(cvc5 cvc5)

if(NOT DEFINED SMT_SWITCH_LIB_TYPE)
  set(SMT_SWITCH_LIB_TYPE SHARED)
endif()

# Where the exported package goes. Each backend installs its own export set
# there, so that a consumer asking for one solver does not have to have the
# others installed as well.
set(SMT_SWITCH_CMAKE_DIR lib/cmake/SmtSwitch)

add_definitions(-DSMT_SWITCH_DIR=${PROJECT_SOURCE_DIR})

set(INCLUDE_DIRS "${PROJECT_SOURCE_DIR}/include")
set(
  SOURCES
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
  "${PROJECT_SOURCE_DIR}/src/utils.cpp"
)

if(SMTLIB_READER)
  # macOS ships a bison far older than this, so this is the one non-solver
  # dependency worth provisioning. flex is not: its 2.6.4 requirement is met
  # by every system copy that is not ancient.
  smt_switch_provision_if_missing(BISON bison 3.7.0)
  find_package(BISON 3.7.0 REQUIRED)
  find_package(FLEX 2.6.4 REQUIRED)

  if(BISON_FOUND)
    get_filename_component(BISON_PARENT_DIR "${BISON_EXECUTABLE}" DIRECTORY)
    message("-- Adding bison lib: ${BISON_PARENT_DIR}/../lib")
    link_directories("${BISON_PARENT_DIR}/../lib/")
  endif()

  bison_target(
    SmtLibParser
    ${PROJECT_SOURCE_DIR}/src/smtlibparser.yy
    ${CMAKE_CURRENT_BINARY_DIR}/smtlibparser.cpp
    DEFINES_FILE ${CMAKE_CURRENT_BINARY_DIR}/smtlibparser.h
  )

  flex_target(
    SmtLibScanner
    ${PROJECT_SOURCE_DIR}/src/smtlibscanner.l
    ${CMAKE_CURRENT_BINARY_DIR}/smtlibscanner.cpp
  )

  add_flex_bison_dependency(SmtLibScanner SmtLibParser)

  # bison's skeleton sets yynerrs_ without reading it. Only that one warning
  # is turned off, rather than all of them with -w, because smtlibparser.yy's
  # actions compile into these generated files too and their warnings are ours.
  set_source_files_properties(
    ${BISON_SmtLibParser_OUTPUTS}
    ${FLEX_SmtLibScanner_OUTPUTS}
    PROPERTIES COMPILE_OPTIONS -Wno-unused-but-set-variable
  )

  # putting generated header files in build dir
  list(APPEND INCLUDE_DIRS "${CMAKE_CURRENT_BINARY_DIR}")

  list(
    APPEND SOURCES
    "${PROJECT_SOURCE_DIR}/src/smtlib_reader.cpp"
    "${BISON_SmtLibParser_OUTPUTS}"
    "${FLEX_SmtLibScanner_OUTPUTS}"
  )
else()
  # if not building with SmtLibReader
  # then exclude the relevant header files from installing
  set(
    EXCLUDE_HEADERS_INSTALL
    PATTERN
    "smtlib_reader.h"
    EXCLUDE
    PATTERN
    "smtlibparser_maps.h"
    EXCLUDE
  )
endif()

add_library(smt-switch "${SMT_SWITCH_LIB_TYPE}" ${SOURCES})
add_library(SmtSwitch::smt-switch ALIAS smt-switch)

# Headers install into include/smt-switch, and consumers spell the prefix:
# #include "smt-switch/smt.h". In the build tree they are found unprefixed,
# hence the two interfaces.
target_include_directories(
  smt-switch
  PUBLIC "$<BUILD_INTERFACE:${INCLUDE_DIRS}>" $<INSTALL_INTERFACE:include>
)
# States the floor for the targets in this tree that consume these headers
target_compile_features(smt-switch PUBLIC cxx_std_11)

set(THREADS_PREFER_PTHREAD_FLAG True)
find_package(Threads)
target_link_libraries(smt-switch PRIVATE Threads::Threads)

# Should we build python bindings
option(BUILD_PYTHON_BINDINGS "Build Python bindings")

# Decide on Python version before setting up googletest
# Otherwise might use wrong version
if(BUILD_PYTHON_BINDINGS)
  # Check for a virtualenv python first
  find_python_in_virtualenv()
  # Want python for building a module, so use Development.Module. See:
  # https://stackoverflow.com/questions/78495429/attempting-to-build-python-binary-modules-on-manylinux-find-packagepython3-on
  find_package(Python 3.10 REQUIRED COMPONENTS Interpreter Development.Module)
endif()

# should we build boolector?
option(BUILD_BTOR "Should we build the libraries for boolector" OFF)
if(BUILD_BTOR)
  smt_switch_provision_if_missing(Boolector boolector)
  # Boolector installs only boolector.h and btortypes.h, but boolector_term.h
  # needs btorcore.h, btornode.h and utils/btornodeiter.h, so the backend
  # needs the source tree in addition to the installed package.
  if(NOT DEFINED Boolector_SOURCE_DIR)
    set(Boolector_SOURCE_DIR "${Boolector_ROOT}/src/boolector")
  endif()
  add_subdirectory(btor)
  set(SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-btor)
  list(APPEND SOLVER_STATIC_LINK_ARGS ${BTOR_STATIC_LINK_ARGS})

  add_definitions(-DBUILD_BTOR)
  add_definitions(-DBOOLECTOR_ROOT=${Boolector_ROOT})
endif()

# should we build bitwuzla?
option(BUILD_BITWUZLA "Should we build the libraries for bitwuzla" OFF)
if(BUILD_BITWUZLA)
  smt_switch_provision_if_missing(Bitwuzla bitwuzla)
  add_subdirectory(bitwuzla)
  set(SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-bitwuzla)

  add_definitions(-DBUILD_BITWUZLA)
  add_definitions(-DBITWUZLA_ROOT=${Bitwuzla_ROOT})
endif()

# should we build cvc5?
option(BUILD_CVC5 "Should we build the libraries for cvc5" OFF)
if(BUILD_CVC5)
  smt_switch_provision_if_missing(cvc5 cvc5)
  add_subdirectory(cvc5)
  set(SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-cvc5)
  list(APPEND SOLVER_STATIC_LINK_ARGS ${CVC5_STATIC_LINK_ARGS})

  add_definitions(-DBUILD_CVC5)
  add_definitions(-DCVC5_ROOT=${cvc5_ROOT})
endif()

# should we build msat?
option(BUILD_MSAT "Should we build the libraries for mathsat" OFF)
if(BUILD_MSAT)
  # Never provisioned. MathSAT is under a custom licence that does not let us
  # fetch it on a user's behalf, so it is the one solver that still has to be
  # installed by hand.
  find_package(MathSAT QUIET)
  if(NOT MathSAT_FOUND)
    message(
      FATAL_ERROR
      "MathSAT was not found, and its licence does not permit downloading it "
      "for you. See the MathSAT section of the README for how to obtain it, "
      "or point --msat-dir at an existing installation."
    )
  endif()
  add_subdirectory(msat)
  set(SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-msat)
  list(APPEND SOLVER_STATIC_LINK_ARGS ${MSAT_STATIC_LINK_ARGS})

  add_definitions(-DBUILD_MSAT)
  add_definitions(-DMATHSAT_ROOT=${MathSAT_ROOT})
endif()

# should we build yices2?
option(BUILD_YICES2 "Should we build the libraries for yices2" OFF)
if(BUILD_YICES2)
  smt_switch_provision_if_missing(Yices2 yices2)
  add_subdirectory(yices2)
  set(SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-yices2)
  list(APPEND SOLVER_STATIC_LINK_ARGS ${YICES2_STATIC_LINK_ARGS})

  add_definitions(-DBUILD_YICES2)
  add_definitions(-DYICES2_ROOT=${Yices2_ROOT})
endif()

# should we build z3?
option(BUILD_Z3 "Should we build the libraries for z3" OFF)
if(BUILD_Z3)
  smt_switch_provision_if_missing(Z3 z3)
  add_definitions(-DBUILD_Z3)
  add_subdirectory(z3)
  set(SOLVER_BACKEND_LIBS ${SOLVER_BACKEND_LIBS} smt-switch-z3)
  list(APPEND SOLVER_STATIC_LINK_ARGS ${Z3_LIBRARY_LOCATION})
endif()

if(BUILD_PYTHON_BINDINGS)
  add_subdirectory(python)
endif()

# should we build the tests
option(BUILD_TESTS "Should we build the test suite" ON)

if(BUILD_TESTS)
  # build testing infrastructure
  enable_testing()

  # Add tests subdirectory
  # The CMakeLists.txt file there sets up googletest
  # and builds all the parametrized tests
  add_subdirectory(tests)
endif()

# install smt-switch
install(TARGETS smt-switch EXPORT SmtSwitchTargets DESTINATION lib)

# install public headers
install(
  DIRECTORY "${PROJECT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  ${EXCLUDE_HEADERS_INSTALL}
)

if(SMTLIB_READER)
  install(FILES "${CMAKE_CURRENT_BINARY_DIR}/smtlibparser.h" DESTINATION include/smt-switch)

  install(FILES "${CMAKE_CURRENT_BINARY_DIR}/location.hh" DESTINATION include/smt-switch)
endif()

######################### Install the CMake package ############################
include(CMakePackageConfigHelpers)

# The component names are the backend suffixes, so that a consumer writes
# find_package(SmtSwitch COMPONENTS cvc5) rather than naming a library. Each
# backend installed its own export set; this is the list of the ones that
# exist, so that asking for a backend this build did not produce fails in
# find_package rather than at link time.
set(SMT_SWITCH_AVAILABLE_COMPONENTS "")
foreach(lib IN LISTS SOLVER_BACKEND_LIBS)
  string(REPLACE "smt-switch-" "" component "${lib}")
  list(APPEND SMT_SWITCH_AVAILABLE_COMPONENTS "${component}")
endforeach()

install(EXPORT SmtSwitchTargets NAMESPACE SmtSwitch:: DESTINATION "${SMT_SWITCH_CMAKE_DIR}")

configure_package_config_file(
  "${PROJECT_SOURCE_DIR}/cmake/SmtSwitchConfig.cmake.in"
  "${CMAKE_CURRENT_BINARY_DIR}/SmtSwitchConfig.cmake"
  INSTALL_DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)

# SameMinorVersion because a minor bump is what this project uses to signal an
# interface change; a patch release stays compatible.
write_basic_package_version_file(
  "${CMAKE_CURRENT_BINARY_DIR}/SmtSwitchConfigVersion.cmake"
  COMPATIBILITY SameMinorVersion
)

install(
  FILES
    "${CMAKE_CURRENT_BINARY_DIR}/SmtSwitchConfig.cmake"
    "${CMAKE_CURRENT_BINARY_DIR}/SmtSwitchConfigVersion.cmake"
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)

# find_dependency runs on the consumer's machine, so the modules that locate
# the solvers have to travel with the package. The remaining modules in cmake/
# are only used while building smt-switch itself.
install(
  FILES
    "${PROJECT_SOURCE_DIR}/cmake/FindBitwuzla.cmake"
    "${PROJECT_SOURCE_DIR}/cmake/FindCaDiCaL.cmake"
    "${PROJECT_SOURCE_DIR}/cmake/FindGMP.cmake"
    "${PROJECT_SOURCE_DIR}/cmake/FindMathSAT.cmake"
    "${PROJECT_SOURCE_DIR}/cmake/FindMPFR.cmake"
    "${PROJECT_SOURCE_DIR}/cmake/FindYices2.cmake"
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)

# uninstall target
# copied from https://gitlab.kitware.com/cmake/community/wikis/FAQ#can-i-do-make-uninstall-with-cmake
if(NOT TARGET uninstall)
  configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/cmake_uninstall.cmake.in"
    "${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake"
    IMMEDIATE
    @ONLY
  )

  add_custom_target(
    uninstall
    COMMAND ${CMAKE_COMMAND} -P ${CMAKE_CURRENT_BINARY_DIR}/cmake_uninstall.cmake
  )
endif()
