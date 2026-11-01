#[=======================================================================[.rst:
FindYices2
----------

Finds the Yices2 SMT solver.

Yices2 is built with autotools and ships neither a CMake package nor a
pkg-config file, so this module looks for the header and the library
directly.

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported target, if found:

``Yices2::yices``
  The Yices2 library.

Unlike :module:`FindGMP`, this module prefers the static archive over the
shared library, and the target carries an ``IMPORTED_LOCATION`` rather than
naming ``yices`` for the linker to resolve.  Yices2 installs ``libyices.a``
and ``libyices.so`` side by side, so resolving by name would quietly pick the
shared library and leave smt-switch with a run-time dependency on Yices2
where it previously had none.  Set ``Yices2_USE_STATIC_LIBS`` to ``OFF`` to
take whichever the linker would normally prefer.

Yices2 is built against GMP, so a consumer has to link :module:`FindGMP`'s
``GMP::gmp`` alongside this target.

Threads the target carries itself.  We configure Yices2 with
``--enable-thread-safety``, so the library we install wants pthreads, and
nothing in what Yices2 installs records that.

A Yices2 built with MCSAT needs LibPoly and CUDD as well.  A shared library
records them itself, but the static archive does not, so this module links a
test program against the library and GMP alone, and if that fails, adds the
LibPoly (``picpoly`` before ``poly``) and CUDD it finds and tries again.  What
it adds, the target carries.  Whether the library actually has MCSAT is left
to ``yices_has_mcsat()`` at run time.

Result Variables
^^^^^^^^^^^^^^^^

``Yices2_FOUND``
  Boolean indicating whether Yices2 was found.
``Yices2_VERSION``
  The version of Yices2 found, read from ``yices.h``.
``Yices2_INCLUDE_DIRS``
  The include directories of Yices2.
``Yices2_LIBRARIES``
  The Yices2 library, and the LibPoly and CUDD libraries it needs, if any.

Cache Variables
^^^^^^^^^^^^^^^

``Yices2_INCLUDE_DIR``
  The directory containing ``yices.h``.
``Yices2_LIBRARY``
  The path to the Yices2 library.
``Yices2_POLY_LIBRARY``, ``Yices2_CUDD_LIBRARY``
  The LibPoly and CUDD libraries, looked for only when the Yices2 library
  does not link without them.

#]=======================================================================]

option(Yices2_USE_STATIC_LIBS "Prefer the static Yices2 archive" ON)

find_path(Yices2_INCLUDE_DIR NAMES yices.h)
if(Yices2_USE_STATIC_LIBS)
  find_library(
    Yices2_LIBRARY
    NAMES "${CMAKE_STATIC_LIBRARY_PREFIX}yices${CMAKE_STATIC_LIBRARY_SUFFIX}" yices
  )
else()
  find_library(Yices2_LIBRARY NAMES yices)
endif()
mark_as_advanced(Yices2_INCLUDE_DIR Yices2_LIBRARY)

# yices.h gives the three parts of its version in this order.
if(Yices2_INCLUDE_DIR)
  file(
    STRINGS "${Yices2_INCLUDE_DIR}/yices.h"
    _yices2_version_lines
    REGEX "^#define __YICES_VERSION(_MAJOR|_PATCHLEVEL)? +[0-9]+"
  )
  set(_yices2_version_parts "")
  foreach(_yices2_line IN LISTS _yices2_version_lines)
    string(REGEX MATCH "[0-9]+" _yices2_number "${_yices2_line}")
    list(APPEND _yices2_version_parts "${_yices2_number}")
  endforeach()
  list(JOIN _yices2_version_parts "." Yices2_VERSION)
endif()

# Whether the library links with GMP alone, and if not, whether it does with
# LibPoly and CUDD too. The results are cached under the library's path, so
# pointing at another Yices2 tests that one afresh.
set(Yices2_LINKS TRUE)
set(_yices2_extra_libraries "")
get_property(_yices2_languages GLOBAL PROPERTY ENABLED_LANGUAGES)
if(Yices2_INCLUDE_DIR AND Yices2_LIBRARY AND "CXX" IN_LIST _yices2_languages)
  find_package(GMP QUIET)
  find_package(Threads QUIET)
  include(CheckCXXSourceCompiles)
  include(CMakePushCheckState)
  cmake_push_check_state(RESET)
  set(CMAKE_REQUIRED_QUIET TRUE)
  set(CMAKE_REQUIRED_INCLUDES "${Yices2_INCLUDE_DIR}")
  set(_yices2_test "#include <yices.h>\nint main() { return yices_has_mcsat(); }")
  string(MD5 _yices2_id "${Yices2_LIBRARY}")
  set(CMAKE_REQUIRED_LIBRARIES "${Yices2_LIBRARY}" GMP::gmp Threads::Threads)
  check_cxx_source_compiles("${_yices2_test}" Yices2_LINKS_ALONE_${_yices2_id})
  if(NOT Yices2_LINKS_ALONE_${_yices2_id})
    find_library(Yices2_POLY_LIBRARY NAMES picpoly poly)
    find_library(Yices2_CUDD_LIBRARY NAMES cudd)
    mark_as_advanced(Yices2_POLY_LIBRARY Yices2_CUDD_LIBRARY)
    set(Yices2_LINKS FALSE)
    if(Yices2_POLY_LIBRARY AND Yices2_CUDD_LIBRARY)
      set(_yices2_extra_libraries "${Yices2_POLY_LIBRARY}" "${Yices2_CUDD_LIBRARY}")
      # after the library that needs them, and before GMP, which LibPoly needs
      list(INSERT CMAKE_REQUIRED_LIBRARIES 1 ${_yices2_extra_libraries})
      check_cxx_source_compiles("${_yices2_test}" Yices2_LINKS_WITH_MCSAT_LIBRARIES_${_yices2_id})
      set(Yices2_LINKS ${Yices2_LINKS_WITH_MCSAT_LIBRARIES_${_yices2_id}})
    endif()
  endif()
  cmake_pop_check_state()
endif()

set(_yices2_reason "")
if(NOT Yices2_LINKS AND _yices2_extra_libraries)
  string(
    CONCAT _yices2_reason
    "${Yices2_LIBRARY} does not link with GMP alone, nor with "
    "${Yices2_POLY_LIBRARY} and ${Yices2_CUDD_LIBRARY}, the LibPoly and CUDD "
    "that a Yices2 built with MCSAT needs."
  )
elseif(NOT Yices2_LINKS)
  string(
    CONCAT _yices2_reason
    "${Yices2_LIBRARY} does not link with GMP alone, and the LibPoly and CUDD "
    "that a Yices2 built with MCSAT needs were not both found."
  )
endif()
include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  Yices2
  REQUIRED_VARS Yices2_LIBRARY Yices2_INCLUDE_DIR Yices2_LINKS
  VERSION_VAR Yices2_VERSION
  REASON_FAILURE_MESSAGE "${_yices2_reason}"
)

if(Yices2_FOUND)
  set(Yices2_INCLUDE_DIRS "${Yices2_INCLUDE_DIR}")
  set(Yices2_LIBRARIES "${Yices2_LIBRARY}" ${_yices2_extra_libraries})

  if(NOT TARGET Yices2::yices)
    find_package(Threads REQUIRED)
    add_library(Yices2::yices UNKNOWN IMPORTED GLOBAL)
    set_target_properties(
      Yices2::yices
      PROPERTIES
        IMPORTED_LOCATION "${Yices2_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${Yices2_INCLUDE_DIR}"
    )
    target_link_libraries(Yices2::yices INTERFACE ${_yices2_extra_libraries} Threads::Threads)
  endif()
endif()
