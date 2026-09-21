#[=======================================================================[.rst:
FindBitwuzla
------------

Finds the Bitwuzla SMT solver.

Bitwuzla is built with Meson and ships no CMake package.  It does install a
pkg-config file, but that file cannot be relied on: Meson generates it from
the library's declared dependencies, so it lists ``symfpu``, a header-only
Meson subproject that installs no ``symfpu.pc`` of its own, and pkg-config
refuses to resolve a ``Requires:`` entry it cannot find.  This module
therefore looks for the libraries directly.

The file is still *read*, though, for two things pkg-config is not needed to
extract: the version, and the names of the SAT backends this Bitwuzla was
built against.  Which of those are present is a build-time choice rather than
a property of the version — CaDiCaL is on by default but can be turned off,
and Kissat, CryptoMiniSat and Gimsatul can be turned on — so the names are
taken from the file rather than assumed.  Anything named but unrecognised is
looked for and linked, and warned about if it cannot be found, which turns an
unexplained pile of undefined symbols into one line at configure time.

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported target, if found:

``Bitwuzla::bitwuzla``
  The Bitwuzla libraries and everything they need.

As in :module:`FindGMP`, the target names its libraries rather than pointing
at the files that were found, so that the linker picks the shared library or
the static archive depending on how the consumer is being linked.

Result Variables
^^^^^^^^^^^^^^^^

``Bitwuzla_FOUND``
  Boolean indicating whether Bitwuzla was found.
``Bitwuzla_VERSION``
  The version of Bitwuzla that was found, if its pkg-config file is
  installed.  Bitwuzla records the version nowhere else: the headers declare
  a ``bitwuzla::version()`` to be called at run time, and nothing more.
``Bitwuzla_INCLUDE_DIRS``
  The include directories of Bitwuzla and its dependencies.
``Bitwuzla_LIBRARY_DIRS``
  The directories holding the libraries of Bitwuzla and its dependencies.
``Bitwuzla_LINK_LIBRARIES``
  The names of those libraries, in the order they have to be linked in.
  Prefer the imported target; reach for these only where a target cannot be
  used, such as when handing the flags to a build system other than CMake.

Cache Variables
^^^^^^^^^^^^^^^

``Bitwuzla_INCLUDE_DIR``
  The directory containing ``bitwuzla/cpp/bitwuzla.h``.
``Bitwuzla_PKGCONFIG_FILE``
  The path to ``bitwuzla.pc``, read for the version and the dependency names
  it states, not resolved through pkg-config.
``Bitwuzla_bitwuzla_LIBRARY``, ``Bitwuzla_bitwuzlals_LIBRARY``,
``Bitwuzla_bitwuzlabv_LIBRARY``, ``Bitwuzla_bitwuzlabb_LIBRARY``
  The paths to the four libraries Bitwuzla installs.

#]=======================================================================]

# GMP and MPFR are not optional in Bitwuzla, so both are always required
# below. CaDiCaL is, and whether it is required is decided further down from
# what the pkg-config file says. Both are reported through REQUIRED_VARS
# rather than as separate failures.
find_package(CaDiCaL QUIET)
find_package(MPFR QUIET)

find_path(Bitwuzla_INCLUDE_DIR NAMES bitwuzla/cpp/bitwuzla.h)

# Bitwuzla splits itself across four archives, and they have to be linked in
# this order: the later ones resolve what the earlier ones leave undefined.
set(_bitwuzla_libraries bitwuzla bitwuzlals bitwuzlabv bitwuzlabb)
set(_bitwuzla_required_vars Bitwuzla_INCLUDE_DIR)
foreach(_bitwuzla_library IN LISTS _bitwuzla_libraries)
  find_library(Bitwuzla_${_bitwuzla_library}_LIBRARY NAMES "${_bitwuzla_library}")
  mark_as_advanced(Bitwuzla_${_bitwuzla_library}_LIBRARY)
  list(APPEND _bitwuzla_required_vars Bitwuzla_${_bitwuzla_library}_LIBRARY)
endforeach()
mark_as_advanced(Bitwuzla_INCLUDE_DIR)

# The only place Bitwuzla records its version is the pkg-config file, which is
# read here rather than queried through pkg-config: the Requires: line above
# makes every query that resolves it fail, and pkg-config need not be
# installed at all. Not required, so a Bitwuzla without the file is still
# found, just without a version.
find_file(
  Bitwuzla_PKGCONFIG_FILE
  NAMES bitwuzla.pc
  PATH_SUFFIXES lib/pkgconfig lib64/pkgconfig share/pkgconfig
)
mark_as_advanced(Bitwuzla_PKGCONFIG_FILE)
if(Bitwuzla_PKGCONFIG_FILE)
  file(STRINGS "${Bitwuzla_PKGCONFIG_FILE}" _bitwuzla_version_line REGEX "^Version:")
  string(REGEX MATCH "[0-9][^ \t]*" Bitwuzla_VERSION "${_bitwuzla_version_line}")
  unset(_bitwuzla_version_line)
endif()

# Which SAT backends a Bitwuzla was built against is a build-time choice, not
# a property of its version: CaDiCaL is on by default but can be turned off,
# and Kissat, CryptoMiniSat and Gimsatul can be turned on. Rather than assume
# the set this project builds, read the names the pkg-config file states.
# They are split across two lines by how Bitwuzla found each one -- pkg-config
# dependencies land in Requires:, compiler-level searches in Libs: -- so read
# both. Only names are taken, not resolved, so the unsatisfiable symfpu entry
# does no harm here.
set(_bitwuzla_stated_deps "")
if(Bitwuzla_PKGCONFIG_FILE)
  file(STRINGS "${Bitwuzla_PKGCONFIG_FILE}" _bitwuzla_requires REGEX "^Requires(\\.private)?:")
  foreach(_bitwuzla_line IN LISTS _bitwuzla_requires)
    string(REGEX REPLACE "^Requires(\\.private)?:" "" _bitwuzla_line "${_bitwuzla_line}")
    # Entries are comma- or space-separated and may carry a version
    # constraint, which is dropped: only the package name matters.
    string(REGEX REPLACE "[<>=]+[ \t]*[0-9][^ \t,]*" "" _bitwuzla_line "${_bitwuzla_line}")
    string(REGEX REPLACE "[ \t,]+" ";" _bitwuzla_line "${_bitwuzla_line}")
    list(APPEND _bitwuzla_stated_deps ${_bitwuzla_line})
  endforeach()

  file(STRINGS "${Bitwuzla_PKGCONFIG_FILE}" _bitwuzla_libs REGEX "^Libs(\\.private)?:")
  foreach(_bitwuzla_line IN LISTS _bitwuzla_libs)
    string(REGEX REPLACE "^Libs(\\.private)?:" "" _bitwuzla_line "${_bitwuzla_line}")
    string(REGEX REPLACE "[ \t]+" ";" _bitwuzla_line "${_bitwuzla_line}")
    foreach(_bitwuzla_token IN LISTS _bitwuzla_line)
      # Either -lfoo, or a path to the archive itself, as a library found by
      # the compiler rather than through pkg-config is recorded in full.
      if(_bitwuzla_token MATCHES "^-l(.+)$")
        list(APPEND _bitwuzla_stated_deps "${CMAKE_MATCH_1}")
      elseif(_bitwuzla_token MATCHES "/lib([^/]+)\\.(a|so|dylib)")
        list(APPEND _bitwuzla_stated_deps "${CMAKE_MATCH_1}")
      endif()
    endforeach()
  endforeach()

  list(REMOVE_DUPLICATES _bitwuzla_stated_deps)
  # Bitwuzla's own libraries, the two it always needs, and symfpu, whose
  # headers are compiled in and which therefore names no library to link.
  list(REMOVE_ITEM _bitwuzla_stated_deps ${_bitwuzla_libraries} gmp mpfr symfpu)
endif()

# CaDiCaL is only required if this Bitwuzla was built against it. Absent a
# pkg-config file there is nothing to go on, so assume the default, which is
# also what this project builds.
set(_bitwuzla_needs_cadical TRUE)
if(Bitwuzla_PKGCONFIG_FILE AND NOT "cadical" IN_LIST _bitwuzla_stated_deps)
  set(_bitwuzla_needs_cadical FALSE)
endif()
list(REMOVE_ITEM _bitwuzla_stated_deps cadical)
if(_bitwuzla_needs_cadical)
  list(APPEND _bitwuzla_required_vars CaDiCaL_FOUND)
endif()

# Anything left is a SAT backend this module does not know about. Link it if
# it can be found, and say so plainly if it cannot, because the alternative is
# a wall of undefined symbols at link time with nothing pointing here.
set(_bitwuzla_extra_libraries "")
set(_bitwuzla_extra_library_dirs "")
foreach(_bitwuzla_dep IN LISTS _bitwuzla_stated_deps)
  find_library(Bitwuzla_${_bitwuzla_dep}_LIBRARY NAMES "${_bitwuzla_dep}")
  mark_as_advanced(Bitwuzla_${_bitwuzla_dep}_LIBRARY)
  if(Bitwuzla_${_bitwuzla_dep}_LIBRARY)
    list(APPEND _bitwuzla_extra_libraries "${_bitwuzla_dep}")
    get_filename_component(_bitwuzla_dep_dir "${Bitwuzla_${_bitwuzla_dep}_LIBRARY}" DIRECTORY)
    list(APPEND _bitwuzla_extra_library_dirs "${_bitwuzla_dep_dir}")
    unset(_bitwuzla_dep_dir)
  else()
    message(
      WARNING
      "Bitwuzla states a dependency on '${_bitwuzla_dep}', which could not be "
      "found. Linking against Bitwuzla will likely fail with undefined "
      "symbols. Set Bitwuzla_${_bitwuzla_dep}_LIBRARY to point at it."
    )
  endif()
endforeach()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  Bitwuzla
  REQUIRED_VARS ${_bitwuzla_required_vars} MPFR_FOUND
  VERSION_VAR Bitwuzla_VERSION
)

if(Bitwuzla_FOUND)
  set(Bitwuzla_INCLUDE_DIRS "${Bitwuzla_INCLUDE_DIR}" ${MPFR_INCLUDE_DIRS})
  get_filename_component(_bitwuzla_library_dir "${Bitwuzla_bitwuzla_LIBRARY}" DIRECTORY)
  set(Bitwuzla_LIBRARY_DIRS "${_bitwuzla_library_dir}" ${MPFR_LIBRARY_DIRS})
  # MPFR brings GMP with it, and the SAT backends come last because the four
  # libraries above call into them. This is the order bitwuzla.pc listed.
  set(Bitwuzla_LINK_LIBRARIES ${_bitwuzla_libraries} ${MPFR_LINK_LIBRARIES})

  if(_bitwuzla_needs_cadical)
    get_filename_component(_cadical_library_dir "${CaDiCaL_LIBRARY}" DIRECTORY)
    list(APPEND Bitwuzla_INCLUDE_DIRS ${CaDiCaL_INCLUDE_DIRS})
    list(APPEND Bitwuzla_LIBRARY_DIRS "${_cadical_library_dir}")
    list(APPEND Bitwuzla_LINK_LIBRARIES cadical)
    unset(_cadical_library_dir)
  endif()

  list(APPEND Bitwuzla_LIBRARY_DIRS ${_bitwuzla_extra_library_dirs})
  list(APPEND Bitwuzla_LINK_LIBRARIES ${_bitwuzla_extra_libraries})

  list(REMOVE_DUPLICATES Bitwuzla_INCLUDE_DIRS)
  list(REMOVE_DUPLICATES Bitwuzla_LIBRARY_DIRS)

  if(NOT TARGET Bitwuzla::bitwuzla)
    add_library(Bitwuzla::bitwuzla INTERFACE IMPORTED GLOBAL)
    set_target_properties(
      Bitwuzla::bitwuzla
      PROPERTIES
        INTERFACE_INCLUDE_DIRECTORIES "${Bitwuzla_INCLUDE_DIRS}"
        INTERFACE_LINK_DIRECTORIES "${Bitwuzla_LIBRARY_DIRS}"
        INTERFACE_LINK_LIBRARIES "${Bitwuzla_LINK_LIBRARIES}"
    )
  endif()

  unset(_bitwuzla_library_dir)
endif()

unset(_bitwuzla_dep)
unset(_bitwuzla_extra_libraries)
unset(_bitwuzla_extra_library_dirs)
unset(_bitwuzla_libs)
unset(_bitwuzla_libraries)
unset(_bitwuzla_library)
unset(_bitwuzla_line)
unset(_bitwuzla_needs_cadical)
unset(_bitwuzla_required_vars)
unset(_bitwuzla_requires)
unset(_bitwuzla_stated_deps)
unset(_bitwuzla_token)
