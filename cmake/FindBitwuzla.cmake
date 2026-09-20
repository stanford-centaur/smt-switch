#[=======================================================================[.rst:
FindBitwuzla
------------

Finds the Bitwuzla SMT solver.

Bitwuzla is built with Meson and ships no CMake package, only a pkg-config
file, so this module wraps ``pkg_check_modules``.  Its ``Requires:`` line
pulls in CaDiCaL, GMP and MPFR, which is why the include and library
directories reported below cover more than Bitwuzla itself.

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported target, if found:

``Bitwuzla::bitwuzla``
  The Bitwuzla library and everything its pkg-config file requires.

As in :module:`FindGMP`, the target names its libraries rather than pointing
at the files that were found, so that the linker picks the shared library or
the static archive depending on how the consumer is being linked.

Result Variables
^^^^^^^^^^^^^^^^

``Bitwuzla_FOUND``
  Boolean indicating whether Bitwuzla was found.
``Bitwuzla_VERSION``
  The version of Bitwuzla that was found.
``Bitwuzla_INCLUDE_DIRS``
  The include directories of Bitwuzla and its requirements.
``Bitwuzla_LIBRARY_DIRS``
  The directories holding the libraries of Bitwuzla and its requirements.
``Bitwuzla_LINK_LIBRARIES``
  The names of those libraries, in the order they have to be linked in.
  Prefer the imported target; reach for these only where a target cannot be
  used, such as when handing the flags to a build system other than CMake.

#]=======================================================================]

find_package(PkgConfig REQUIRED)

# pkg_check_modules is not a find_* command, so it does not consult
# Bitwuzla_ROOT the way find_library would. Feed the hint in through
# CMAKE_PREFIX_PATH, which FindPkgConfig does fold into PKG_CONFIG_PATH, and
# put it back afterwards so the rest of the project is unaffected.
#
# CaDiCaL comes along for the ride: bitwuzla.pc names it in Requires:, and
# pkg-config resolves that itself, so cadical.pc has to be reachable too.
# Each dependency has its own prefix, so that is a second directory.
set(_bitwuzla_saved_prefix_path "${CMAKE_PREFIX_PATH}")
foreach(
  _bitwuzla_hint
  IN
  ITEMS "${CaDiCaL_ROOT}" "$ENV{CaDiCaL_ROOT}" "${Bitwuzla_ROOT}" "$ENV{Bitwuzla_ROOT}"
)
  if(_bitwuzla_hint)
    list(INSERT CMAKE_PREFIX_PATH 0 "${_bitwuzla_hint}")
  endif()
endforeach()
unset(_bitwuzla_hint)

pkg_check_modules(PC_Bitwuzla QUIET bitwuzla)

set(CMAKE_PREFIX_PATH "${_bitwuzla_saved_prefix_path}")
unset(_bitwuzla_saved_prefix_path)

set(Bitwuzla_VERSION "${PC_Bitwuzla_VERSION}")
set(Bitwuzla_INCLUDE_DIRS "${PC_Bitwuzla_INCLUDE_DIRS}")
set(Bitwuzla_LIBRARY_DIRS "${PC_Bitwuzla_LIBRARY_DIRS}")
set(Bitwuzla_LINK_LIBRARIES "${PC_Bitwuzla_LIBRARIES}")

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  Bitwuzla
  REQUIRED_VARS Bitwuzla_LINK_LIBRARIES Bitwuzla_INCLUDE_DIRS
  VERSION_VAR Bitwuzla_VERSION
)

if(Bitwuzla_FOUND AND NOT TARGET Bitwuzla::bitwuzla)
  add_library(Bitwuzla::bitwuzla INTERFACE IMPORTED GLOBAL)
  set_target_properties(
    Bitwuzla::bitwuzla
    PROPERTIES
      INTERFACE_INCLUDE_DIRECTORIES "${Bitwuzla_INCLUDE_DIRS}"
      INTERFACE_LINK_DIRECTORIES "${Bitwuzla_LIBRARY_DIRS}"
      INTERFACE_LINK_LIBRARIES "${Bitwuzla_LINK_LIBRARIES}"
  )
endif()
