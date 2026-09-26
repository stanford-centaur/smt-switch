#[=======================================================================[.rst:
ProvisionDeps
-------------

Builds the dependencies this project could not find.

``find_package`` runs at configure time, but ``ExternalProject_Add`` produces
targets that only run at build time, so a dependency cannot be provisioned by
the build that needs it.  The driver in ``cmake/provision/`` is therefore run
here as a nested project, to completion, before the lookup that needs it.

.. command:: smt_switch_provision_if_missing

  .. code-block:: cmake

    smt_switch_provision_if_missing(<Package> <target> [<find_package args>...])

  Looks for ``<Package>``; if it is not there and ``SMT_SWITCH_AUTO_DEPS`` is
  on, builds ``<target>`` and everything it depends on.  Does nothing when the
  package is already installed, so a ``--<solver>-dir`` pointing at one costs
  nothing.  The caller is expected to follow with its own ``REQUIRED`` lookup,
  which is what reports a failure that provisioning did not fix.

Cache Variables
^^^^^^^^^^^^^^^

``SMT_SWITCH_DEPS_DIR``
  Where the prefixes live, ``<source>/deps`` by default.  Nothing else fixes
  the location: this is also what the ``<Package>_ROOT`` defaults in the top
  level ``CMakeLists.txt`` are relative to, so pointing it elsewhere moves
  both where dependencies are looked for and where they are built.

  It is deliberately not under the build directory, which is what
  ``ExternalProject`` would do by default.  Deleting a build directory is
  routine and rebuilding cvc5 is not, and with the prefixes outside it a
  wipe costs nothing: every dependency is still found and the driver is
  never even configured.

  An existing tree cannot simply be moved, though.  Installed packages record
  the prefix they were built against -- Boolector's CMake package names
  btor2tools' and CaDiCaL's archives by absolute path, and the Bitwuzla and
  Z3 pkg-config files carry an absolute ``prefix=`` -- so a relocated tree
  has to be rebuilt rather than carried across.  Provisioning into a new
  location from scratch works as it should.

#]=======================================================================]

option(SMT_SWITCH_AUTO_DEPS "Download and build dependencies that cannot be found" ON)
option(SMT_SWITCH_ALLOW_GPL "Permit automatic download of GPL-licensed dependencies (Yices2)" OFF)

set(
  SMT_SWITCH_DEPS_DIR
  "${PROJECT_SOURCE_DIR}/deps"
  CACHE PATH
  "Where provisioned dependencies are installed"
)

# The driver only declares the dependencies it is told about, so that a build
# wanting one solver does not get an empty prefix for all eight. Since the
# backends are reached one at a time, the list grows as we go and the driver
# is reconfigured with it; that costs a fraction of a second, and only
# happens when something actually has to be built.
#
# A global property rather than a variable, because it has to outlive the
# function call that appends to it.
define_property(
  GLOBAL
  PROPERTY SMT_SWITCH_PROVISION_TARGETS
  BRIEF_DOCS "Dependencies the provisioner has been asked for so far"
  FULL_DOCS "Accumulated so that each run of the driver declares all of them"
)

# configure.sh names the Boolector options after the backend directory rather
# than the solver, so --btor-dir and not --boolector-dir. Every other target
# is spelled the same way in both places.
function(_smt_switch_dir_flag target output)
  if(target STREQUAL "boolector")
    set(${output} "btor" PARENT_SCOPE)
  else()
    set(${output} "${target}" PARENT_SCOPE)
  endif()
endfunction()

function(_smt_switch_run_provision_driver target)
  set(_source_dir "${PROJECT_SOURCE_DIR}/cmake/provision")
  # Beside the prefixes it manages, not under the build directory. The stamps
  # that make provisioning incremental live in the prefixes, but the
  # generator's own record of what it has run does not: wipe that and Ninja
  # re-runs every step, because an edge whose command line it cannot find in
  # its log counts as dirty. Keeping the two together means deleting the
  # build directory costs nothing, which is the whole point of the
  # dependencies living outside it.
  set(_binary_dir "${SMT_SWITCH_DEPS_DIR}/.provision")

  get_property(_targets GLOBAL PROPERTY SMT_SWITCH_PROVISION_TARGETS)
  if(NOT target IN_LIST _targets)
    list(APPEND _targets "${target}")
    set_property(GLOBAL PROPERTY SMT_SWITCH_PROVISION_TARGETS "${_targets}")
  endif()
  # Comma-separated: a semicolon would split the -D into two arguments.
  string(REPLACE ";" "," _target_list "${_targets}")

  # Forwarded so that a dependency is built with the toolchain that will
  # link it. The generator is passed separately from the cache variables
  # because it has its own flag.
  set(
    _arguments
    "-DSMT_SWITCH_DEPS_DIR=${SMT_SWITCH_DEPS_DIR}"
    "-DSMT_SWITCH_PROVISION_TARGETS=${_target_list}"
  )
  foreach(
    _variable
    IN
    ITEMS
      CMAKE_C_COMPILER
      CMAKE_CXX_COMPILER
      CMAKE_C_COMPILER_LAUNCHER
      CMAKE_CXX_COMPILER_LAUNCHER
      CMAKE_TOOLCHAIN_FILE
      CMAKE_OSX_ARCHITECTURES
      CMAKE_OSX_DEPLOYMENT_TARGET
      CMAKE_OSX_SYSROOT
      Python_EXECUTABLE
  )
    if(DEFINED ${_variable})
      list(APPEND _arguments "-D${_variable}=${${_variable}}")
    endif()
  endforeach()
  if(CMAKE_MAKE_PROGRAM)
    list(APPEND _arguments "-DCMAKE_MAKE_PROGRAM=${CMAKE_MAKE_PROGRAM}")
  endif()

  # The dependencies are built once, whichever configurations smt-switch
  # itself is built in. A multi-config generator would build them as its
  # first configuration, Debug, since nothing below asks for another. And
  # as the directory outlives the build directory, switching between the two
  # Ninja generators would otherwise fail on a generator mismatch.
  set(_generator "${CMAKE_GENERATOR}")
  if(_generator STREQUAL "Ninja Multi-Config")
    set(_generator "Ninja")
  endif()

  execute_process(
    COMMAND
      "${CMAKE_COMMAND}" -G "${_generator}" -S "${_source_dir}" -B "${_binary_dir}" ${_arguments}
    RESULT_VARIABLE _result
  )
  if(NOT _result EQUAL 0)
    message(FATAL_ERROR "Could not configure the dependency provisioner in ${_binary_dir}")
  endif()

  message(STATUS "Provisioning ${target}; this may take a while")
  # One dependency at a time: each sub-build is already parallel, and nesting
  # -j inside -j oversubscribes badly.
  execute_process(
    COMMAND "${CMAKE_COMMAND}" --build "${_binary_dir}" --target "${target}"
    RESULT_VARIABLE _result
  )
  if(NOT _result EQUAL 0)
    _smt_switch_dir_flag("${target}" _flag)
    message(
      FATAL_ERROR
      "Could not build ${target}. Its log is under "
      "${SMT_SWITCH_DEPS_DIR}/${target}/src/${target}-stamp. Build it "
      "yourself and point --${_flag}-dir at it, or pass --no-auto-deps to "
      "turn provisioning off."
    )
  endif()
endfunction()

function(smt_switch_provision_if_missing package target)
  get_cmake_property(_cache_before CACHE_VARIABLES)
  find_package("${package}" QUIET ${ARGN})
  if(${package}_FOUND)
    return()
  endif()
  get_cmake_property(_cache_after CACHE_VARIABLES)

  # A rejected path stays in the cache and is never searched for again, so
  # the copy about to be provisioned would be ignored. Only this package's
  # own entries: what its lookup found on the way to failing is still good.
  list(REMOVE_ITEM _cache_after ${_cache_before})
  foreach(_entry IN LISTS _cache_after)
    if(_entry MATCHES "^${package}_")
      unset(${_entry} CACHE)
    endif()
  endforeach()

  _smt_switch_dir_flag("${target}" _flag)
  if(NOT SMT_SWITCH_AUTO_DEPS)
    message(
      FATAL_ERROR
      "${package} was not found and automatic provisioning is off. Point "
      "--${_flag}-dir at an existing installation, or drop --no-auto-deps."
    )
  endif()

  # Yices2 is GPLv3. Everything else here is permissively licensed, so this
  # is the one dependency that is not fetched unless it is asked for.
  if(target STREQUAL "yices2" AND NOT SMT_SWITCH_ALLOW_GPL)
    message(
      FATAL_ERROR
      "Yices2 was not found. It is licensed under the GPLv3, so it is only "
      "downloaded when you say so: pass --allow-gpl to accept that, or "
      "point --yices2-dir at an installation you built yourself."
    )
  endif()

  _smt_switch_run_provision_driver("${target}")
endfunction()
