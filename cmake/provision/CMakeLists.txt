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

cmake_minimum_required(VERSION 3.14)
project(smt-switch-deps LANGUAGES NONE)

include(ExternalProject)
include("${CMAKE_CURRENT_SOURCE_DIR}/versions.cmake")

# CMake only started verifying certificates by default in 3.31, and we support
# 3.14, so say so rather than leave it to the version in use.
set(CMAKE_TLS_VERIFY TRUE)

if(NOT SMT_SWITCH_DEPS_DIR)
  message(FATAL_ERROR "SMT_SWITCH_DEPS_DIR must be set to the directory holding the prefixes")
endif()

# Only the dependencies that were asked for are declared. ExternalProject
# creates a prefix skeleton for every target at configure time, so declaring
# all of them would leave empty deps/<name> directories for solvers this
# build never wanted -- and each of those is a <Package>_ROOT pointing at
# nothing.
#
# Passed comma-separated, because a semicolon would split the -D argument.
set(SMT_SWITCH_PROVISION_TARGETS "" CACHE STRING "Comma-separated dependencies to declare")
string(REPLACE "," ";" _requested "${SMT_SWITCH_PROVISION_TARGETS}")

set(_cadical_needs "")
set(_btor2tools_needs "")
set(_boolector_needs cadical btor2tools)
set(_bitwuzla_needs cadical)
set(_cvc5_needs cadical)
set(_z3_needs "")
set(_yices2_needs "")
set(_bison_needs "")

# Close over dependencies, so that asking for boolector also declares the two
# it is built against. Iterated to a fixed point rather than expanded once,
# so that it keeps working if a dependency ever gains one of its own.
# list(POP_FRONT) would be tidier but wants CMake 3.15.
set(_wanted ${_requested})
foreach(_target IN LISTS _wanted)
  if(NOT DEFINED _${_target}_needs)
    message(FATAL_ERROR "There is no provisioning recipe for '${_target}'")
  endif()
endforeach()

set(_growing TRUE)
while(_growing)
  set(_growing FALSE)
  foreach(_target IN LISTS _wanted)
    foreach(_need IN LISTS _${_target}_needs)
      if(NOT _need IN_LIST _wanted)
        list(APPEND _wanted "${_need}")
        set(_growing TRUE)
      endif()
    endforeach()
  endforeach()
endwhile()

include(ProcessorCount)
ProcessorCount(SMT_SWITCH_DEPS_JOBS)
if(SMT_SWITCH_DEPS_JOBS EQUAL 0)
  set(SMT_SWITCH_DEPS_JOBS 1)
endif()

# Forwarded to every nested CMake build, so that a dependency is built with
# the same toolchain as the project that will link it. Only variables that
# were actually set are passed on, or an empty one would override a default
# the sub-build would otherwise pick for itself.
#
# CMAKE_BUILD_TYPE is deliberately absent: cvc5 declares its own build types
# and fails on anything outside them, so a blanket Release would break it.
# Each dependency picks its own default instead.
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
# CMAKE_INSTALL_LIBDIR keeps libraries out of a lib64 subdirectory, which the
# find modules do not look in; the policy minimum lets projects whose
# cmake_minimum_required predates 3.10 still configure.
list(
  APPEND COMMON_CMAKE_ARGS
  -DBUILD_SHARED_LIBS=OFF
  -DCMAKE_INSTALL_LIBDIR=lib
  -DCMAKE_POLICY_VERSION_MINIMUM=3.10
  -DCMAKE_POSITION_INDEPENDENT_CODE=ON
)

# With PREFIX set and nothing else overridden, ExternalProject puts the
# sources at <prefix>/src/<name> and computes <prefix> as the install
# directory. That is the layout the find modules already expect. Two traps:
# the <name> in those paths is the target name, not the prefix directory, so
# the two must match; and ExternalProject computes INSTALL_DIR but does not
# apply it, so every CMake recipe has to pass CMAKE_INSTALL_PREFIX itself.
function(smt_switch_dependency name)
  if(NOT name IN_LIST _wanted)
    return()
  endif()
  string(TOUPPER "${name}" _upper_name)
  ExternalProject_Add(
    "${name}"
    PREFIX "${SMT_SWITCH_DEPS_DIR}/${name}"
    # CMAKE_ARGS is itself a CMake list, so a semicolon inside one argument --
    # a CMAKE_PREFIX_PATH naming two prefixes -- would split it in two. The
    # recipes below write those with | and ExternalProject puts them back.
    LIST_SEPARATOR |
    # Supplied here rather than by each recipe, so that a dependency cannot
    # be added without one.
    URL_HASH "SHA256=${${_upper_name}_SHA256}"
    DOWNLOAD_EXTRACT_TIMESTAMP TRUE
    USES_TERMINAL_DOWNLOAD TRUE
    USES_TERMINAL_CONFIGURE TRUE
    USES_TERMINAL_BUILD TRUE
    USES_TERMINAL_INSTALL TRUE
    ${ARGN}
  )
endfunction()

# Where each dependency will be installed, for the recipes that have to name
# a sibling's prefix, and the point at which a pin without a hash is caught.
# Every dependency is checked, not only the ones this build wants, so that
# adding one without a hash fails whatever is being built.
foreach(
  _dependency
  cadical
  btor2tools
  boolector
  bitwuzla
  cvc5
  z3
  yices2
  bison
)
  string(TOUPPER "${_dependency}" _upper)
  set(${_upper}_PREFIX "${SMT_SWITCH_DEPS_DIR}/${_dependency}")
  if(NOT ${_upper}_SHA256)
    message(
      FATAL_ERROR
      "${_dependency} has no ${_upper}_SHA256 in versions.cmake, so what it "
      "downloads cannot be checked. Get one from "
      "`cmake -P cmake/provision/refresh-hashes.cmake ${_dependency}`."
    )
  endif()
endforeach()

# ---------------------------------------------------------------- cadical --
# No install target and no build system beyond a hand-written configure
# script, so the install is a cmake -P step. Built with -fPIC because it ends
# up inside shared libraries.
smt_switch_dependency(
  cadical
  URL "${CADICAL_URL}"
  CONFIGURE_COMMAND <SOURCE_DIR>/configure "CXXFLAGS=-fPIC"
  BUILD_COMMAND make -j${SMT_SWITCH_DEPS_JOBS}
  BUILD_IN_SOURCE TRUE
  INSTALL_COMMAND
    "${CMAKE_COMMAND}" -DSOURCE_DIR=<SOURCE_DIR> -DINSTALL_DIR=<INSTALL_DIR> -P
    "${CMAKE_CURRENT_SOURCE_DIR}/install-cadical.cmake"
)

# ------------------------------------------------------------- btor2tools --
smt_switch_dependency(
  btor2tools
  URL "${BTOR2TOOLS_URL}"
  CMAKE_ARGS ${COMMON_CMAKE_ARGS} -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
  BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> -j${SMT_SWITCH_DEPS_JOBS}
)

# -------------------------------------------------------------- boolector --
smt_switch_dependency(
  boolector
  URL "${BOOLECTOR_URL}"
  DEPENDS cadical btor2tools
  CMAKE_ARGS
    ${COMMON_CMAKE_ARGS}
    -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
    "-DCMAKE_PREFIX_PATH=${CADICAL_PREFIX}|${BTOR2TOOLS_PREFIX}"
    -DUSE_CADICAL=ON
  BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> -j${SMT_SWITCH_DEPS_JOBS}
)

# ------------------------------------------------------------------- cvc5 --
# ENABLE_AUTO_DOWNLOAD lets cvc5 fetch the dependencies of its own that we do
# not provision; USE_POLY brings in libpoly for nonlinear arithmetic.
smt_switch_dependency(
  cvc5
  URL "${CVC5_URL}"
  DEPENDS cadical
  CMAKE_ARGS
    ${COMMON_CMAKE_ARGS}
    -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
    "-DCMAKE_PREFIX_PATH=${CADICAL_PREFIX}"
    -DENABLE_AUTO_DOWNLOAD=ON
    -DUSE_POLY=ON
  BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> -j${SMT_SWITCH_DEPS_JOBS}
)

# --------------------------------------------------------------------- z3 --
smt_switch_dependency(
  z3
  URL "${Z3_URL}"
  CMAKE_ARGS ${COMMON_CMAKE_ARGS} -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR> -DZ3_BUILD_LIBZ3_SHARED=OFF
  BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> -j${SMT_SWITCH_DEPS_JOBS}
)

# --------------------------------------------------------------- bitwuzla --
# Meson, driven through Bitwuzla's own configure.py. CaDiCaL ships no
# pkg-config file and Bitwuzla looks for it with the compiler before falling
# back to pkg-config, so its prefix goes on the compiler's search path. See
# cmake/FindBitwuzla.cmake for the whole story, and the patch below for why
# putting it there is not enough on its own.
#
# Prepended to whatever the environment already holds rather than replacing
# it, because `cmake -E env VAR=...` hands the child only what it is given.
# On macOS these are how Homebrew's headers and libraries are reachable at
# all, so overwriting them loses GMP and MPFR and the link fails.
function(smt_switch_prepend_path variable directory output)
  set(value "${directory}")
  if(NOT "$ENV{${variable}}" STREQUAL "")
    set(value "${value}:$ENV{${variable}}")
  endif()
  set(${output} "${variable}=${value}" PARENT_SCOPE)
endfunction()

smt_switch_prepend_path(CPATH "${CADICAL_PREFIX}/include" BITWUZLA_CPATH)
smt_switch_prepend_path(LIBRARY_PATH "${CADICAL_PREFIX}/lib" BITWUZLA_LIBRARY_PATH)

smt_switch_dependency(
  bitwuzla
  URL "${BITWUZLA_URL}"
  DEPENDS cadical
  # patch rather than a substitution, so that a release whose text has moved
  # on stops the build instead of silently leaving Bitwuzla to fetch and
  # build a second CaDiCaL of its own.
  PATCH_COMMAND
    patch -p1 --forward -i
    "${CMAKE_CURRENT_SOURCE_DIR}/patches/bitwuzla-search-library-path.patch"
  CONFIGURE_COMMAND
    "${CMAKE_COMMAND}" -E env "${BITWUZLA_CPATH}" "${BITWUZLA_LIBRARY_PATH}"
    "${Python_EXECUTABLE}" <SOURCE_DIR>/configure.py --prefix <INSTALL_DIR>
  BUILD_COMMAND
    "${CMAKE_COMMAND}" -E env "${BITWUZLA_CPATH}" "${BITWUZLA_LIBRARY_PATH}" meson compile -C
    <SOURCE_DIR>/build
  INSTALL_COMMAND meson install -C <SOURCE_DIR>/build
  BUILD_IN_SOURCE TRUE
)

# ----------------------------------------------------------------- yices2 --
# Autotools, but the release archive carries no configure script, so autoconf
# runs first. LDCONFIG lives in /usr/sbin, which is not always on a user's
# PATH, and all it would do is refresh symlinks next to the staged library.
smt_switch_dependency(
  yices2
  URL "${YICES2_URL}"
  CONFIGURE_COMMAND autoconf
  COMMAND <SOURCE_DIR>/configure --enable-thread-safety --prefix=<INSTALL_DIR>
  BUILD_COMMAND make build_dir=build BUILD=build -j${SMT_SWITCH_DEPS_JOBS}
  INSTALL_COMMAND make build_dir=build BUILD=build prefix=<INSTALL_DIR> LDCONFIG=true install
  BUILD_IN_SOURCE TRUE
)

# ------------------------------------------------------------------ bison --
smt_switch_dependency(
  bison
  URL "${BISON_URL}"
  CONFIGURE_COMMAND <SOURCE_DIR>/configure --prefix=<INSTALL_DIR>
  BUILD_COMMAND make -j${SMT_SWITCH_DEPS_JOBS}
  INSTALL_COMMAND make install
  BUILD_IN_SOURCE TRUE
)
