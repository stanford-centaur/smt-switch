# Builds the dependencies smt-switch could not find.
#
# A separate project rather than part of the main build, driven from
# cmake/ProvisionDeps.cmake through execute_process. ExternalProject produces
# build-time targets, but find_package runs at configure time, so a
# dependency has to be finished before the main project's configure reaches
# the backend that needs it. The usual answer, a superbuild, would move the
# binary directory to build/<prefix>/smt-switch-build and break every path CI
# knows -- `ninja -C build`, `ctest --test-dir build`, `build/python/*.whl`.
#
# LANGUAGES NONE: nothing is compiled here, only sub-builds are driven, and
# the compiler each of those uses is forwarded in rather than detected twice.

cmake_minimum_required(VERSION 3.16)
project(smt-switch-deps LANGUAGES NONE)

include(ExternalProject)
include("${CMAKE_CURRENT_LIST_DIR}/Helpers.cmake")
smt_switch_dependencies(_dependencies)
foreach(_dependency IN LISTS _dependencies)
  include("${CMAKE_CURRENT_LIST_DIR}/${_dependency}/pin.cmake")
endforeach()

# The project's find modules live one directory up; the yices2 recipe needs
# FindGMP.
list(APPEND CMAKE_MODULE_PATH "${CMAKE_CURRENT_LIST_DIR}/..")

# CMake only started verifying certificates by default in 3.31, and we support
# 3.16, so say so rather than leave it to the version in use.
set(CMAKE_TLS_VERIFY TRUE)

if(NOT SMT_SWITCH_DEPS_DIR)
  message(FATAL_ERROR "SMT_SWITCH_DEPS_DIR must be set to the directory holding the prefixes")
endif()

# The library directory a dependency using GNUInstallDirs picks for itself,
# for the recipes that have to find something in it afterwards. Worked out
# from the CMAKE_SIZEOF_VOID_P and CMAKE_LIBRARY_ARCHITECTURE the main project
# forwards, since nothing here enables a language. The prefix matters too:
# Debian's multiarch directory is used only for /usr, so it is judged against
# the prefixes the dependencies actually install into. Nothing here installs
# anything itself.
set(CMAKE_INSTALL_PREFIX "${SMT_SWITCH_DEPS_DIR}")
include(GNUInstallDirs)

# Only the dependencies that were asked for are declared. ExternalProject
# creates a prefix skeleton for every target at configure time, so declaring
# all of them would leave empty deps/<name> directories for solvers this
# build never wanted -- and each of those is a <Package>_ROOT pointing at
# nothing.
#
# Passed comma-separated, because a semicolon would split the -D argument.
set(SMT_SWITCH_PROVISION_TARGETS "" CACHE STRING "Comma-separated dependencies to declare")
string(REPLACE "," ";" _requested "${SMT_SWITCH_PROVISION_TARGETS}")

foreach(_target IN LISTS _requested)
  if(NOT _target IN_LIST _dependencies)
    message(FATAL_ERROR "There is no provisioning recipe for '${_target}'")
  endif()
endforeach()

include(ProcessorCount)
ProcessorCount(SMT_SWITCH_DEPS_JOBS)
if(SMT_SWITCH_DEPS_JOBS EQUAL 0)
  set(SMT_SWITCH_DEPS_JOBS 1)
endif()

# Forwarded to every nested CMake build, so that a dependency is built with
# the same toolchain as the project that will link it. Only variables that
# were actually set are passed on, or an empty one would override a default
# the sub-build would otherwise pick for itself.
set(
  _forwarded_variables
  CMAKE_C_COMPILER
  CMAKE_CXX_COMPILER
  CMAKE_C_COMPILER_LAUNCHER
  CMAKE_CXX_COMPILER_LAUNCHER
  CMAKE_TOOLCHAIN_FILE
  CMAKE_OSX_ARCHITECTURES
  CMAKE_OSX_DEPLOYMENT_TARGET
  CMAKE_OSX_SYSROOT
)
set(COMMON_CMAKE_ARGS "")
foreach(_variable IN LISTS _forwarded_variables)
  if(DEFINED ${_variable})
    list(APPEND COMMON_CMAKE_ARGS "-D${_variable}=${${_variable}}")
  endif()
endforeach()

# Passed to every CMake dependency.
list(
  APPEND COMMON_CMAKE_ARGS
  -DBUILD_SHARED_LIBS=OFF
  -DCMAKE_BUILD_TYPE=Release
  -DCMAKE_POSITION_INDEPENDENT_CODE=ON
)

# Only for the dependencies whose cmake_minimum_required predates what CMake
# still supports: Boolector and the btor2tools it builds both ask for 3.3.
# cvc5 and z3 both ask for 3.16 and would report it as an unused variable.
set(POLICY_VERSION_MINIMUM 3.10)
set(POLICY_CMAKE_ARGS -DCMAKE_POLICY_VERSION_MINIMUM=${POLICY_VERSION_MINIMUM})

# Keeps the archives' timestamps, which CMake before 3.24 always does and
# has no option to ask for.
set(_extract_timestamp_option "")
if(NOT CMAKE_VERSION VERSION_LESS 3.24)
  set(_extract_timestamp_option DOWNLOAD_EXTRACT_TIMESTAMP TRUE)
endif()

# With PREFIX set and nothing else overridden, ExternalProject puts the
# sources at <prefix>/src/<name> and computes <prefix> as the install
# directory. That is the layout the find modules already expect. Two traps:
# the <name> in those paths is the target name, not the prefix directory, so
# the two must match; and ExternalProject computes INSTALL_DIR but does not
# apply it, so every CMake recipe has to pass CMAKE_INSTALL_PREFIX itself.
function(smt_switch_dependency name)
  if(NOT name IN_LIST _requested)
    return()
  endif()
  string(TOUPPER "${name}" _upper_name)
  ExternalProject_Add(
    "${name}"
    PREFIX "${SMT_SWITCH_DEPS_DIR}/${name}"
    # Supplied here rather than by each recipe, so that a dependency cannot
    # be added without one.
    URL_HASH "SHA256=${${_upper_name}_SHA256}"
    ${_extract_timestamp_option}
    USES_TERMINAL_DOWNLOAD TRUE
    USES_TERMINAL_CONFIGURE TRUE
    USES_TERMINAL_BUILD TRUE
    USES_TERMINAL_INSTALL TRUE
    ${ARGN}
  )
endfunction()

# Builds a `VAR=value` argument for `cmake -E env`, prepended to whatever the
# environment already holds rather than replacing it, because that command
# hands the child only what it is given. On macOS these variables are how
# Homebrew's headers and libraries are reachable at all, so overwriting them
# loses GMP and MPFR and the link fails.
function(smt_switch_prepend_path variable directory output)
  set(value "${directory}")
  if(NOT "$ENV{${variable}}" STREQUAL "")
    set(value "${value}:$ENV{${variable}}")
  endif()
  set(${output} "${variable}=${value}" PARENT_SCOPE)
endfunction()

# Where a pin without a hash is caught. Every dependency is checked, not only
# the ones this build wants, so that adding one without a hash fails whatever
# is being built.
foreach(_dependency IN LISTS _dependencies)
  string(TOUPPER "${_dependency}" _upper)
  if(NOT ${_upper}_SHA256)
    message(
      FATAL_ERROR
      "${_dependency} has no CHECKSUM in "
      "cmake/provision/${_dependency}/pin.cmake, so what it "
      "downloads cannot be checked. Record one with "
      "`cmake -P cmake/provision/update-checksums.cmake ${_dependency}`."
    )
  endif()
endforeach()

foreach(_dependency IN LISTS _dependencies)
  include("${CMAKE_CURRENT_LIST_DIR}/${_dependency}/recipe.cmake")
endforeach()
