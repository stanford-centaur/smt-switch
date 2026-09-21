#[=======================================================================[.rst:
FindMPFR
--------

Finds the GNU Multiple Precision Floating-Point Reliable Library (MPFR).

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported target, if found:

``MPFR::mpfr``
  The MPFR library.  It depends on GMP, so linking this target alone is
  enough, and the two libraries reach the link line in an order that resolves.

As in :module:`FindGMP`, the target names its library rather than pointing at
the file that was found, so that the linker picks the shared library or the
static archive depending on how the consumer is being linked.

Result Variables
^^^^^^^^^^^^^^^^

``MPFR_FOUND``
  Boolean indicating whether MPFR was found.
``MPFR_VERSION``
  The version of MPFR that was found.
``MPFR_INCLUDE_DIRS``
  The include directories of MPFR.
``MPFR_LIBRARY_DIRS``
  The directories holding the libraries of MPFR.
``MPFR_LINK_LIBRARIES``
  The names of those libraries, in the order they have to be linked in.
  Prefer the imported target; reach for these only where a target cannot be
  used, such as when handing the flags to a build system other than CMake.

Cache Variables
^^^^^^^^^^^^^^^

``MPFR_INCLUDE_DIR``
  The directory containing ``mpfr.h``.
``MPFR_LIBRARY``
  The path to the MPFR library.

#]=======================================================================]

# libmpfr is built on top of libgmp and mpfr.h includes gmp.h, so MPFR cannot
# be used without it.
# Reported through REQUIRED_VARS below, so that a missing GMP surfaces as part
# of MPFR not being found rather than as a separate failure.
find_package(GMP QUIET)

find_path(MPFR_INCLUDE_DIR NAMES mpfr.h)
find_library(MPFR_LIBRARY NAMES mpfr)
mark_as_advanced(MPFR_INCLUDE_DIR MPFR_LIBRARY)

# The version is three separate macros in mpfr.h; MPFR_VERSION_STRING joins
# them, but it may carry a suffix such as "-p1" that CMake cannot compare.
if(MPFR_INCLUDE_DIR AND EXISTS "${MPFR_INCLUDE_DIR}/mpfr.h")
  file(
    STRINGS "${MPFR_INCLUDE_DIR}/mpfr.h"
    _mpfr_version_line
    REGEX "^#define MPFR_VERSION_STRING "
  )
  string(REGEX MATCH "[0-9]+\\.[0-9]+\\.[0-9]+" MPFR_VERSION "${_mpfr_version_line}")
  unset(_mpfr_version_line)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  MPFR
  REQUIRED_VARS MPFR_LIBRARY MPFR_INCLUDE_DIR GMP_FOUND
  VERSION_VAR MPFR_VERSION
)

if(MPFR_FOUND)
  get_filename_component(_mpfr_library_dir "${MPFR_LIBRARY}" DIRECTORY)

  set(MPFR_INCLUDE_DIRS "${MPFR_INCLUDE_DIR}" ${GMP_INCLUDE_DIRS})
  set(MPFR_LIBRARY_DIRS "${_mpfr_library_dir}" ${GMP_LIBRARY_DIRS})
  list(REMOVE_DUPLICATES MPFR_INCLUDE_DIRS)
  list(REMOVE_DUPLICATES MPFR_LIBRARY_DIRS)
  # libmpfr has to be linked before libgmp: it references symbols from GMP,
  # and an archive only resolves what is undefined by the time the linker
  # reaches it.
  set(MPFR_LINK_LIBRARIES mpfr ${GMP_LINK_LIBRARIES})

  if(NOT TARGET MPFR::mpfr)
    add_library(MPFR::mpfr INTERFACE IMPORTED GLOBAL)
    set_target_properties(
      MPFR::mpfr
      PROPERTIES
        INTERFACE_INCLUDE_DIRECTORIES "${MPFR_INCLUDE_DIR}"
        INTERFACE_LINK_DIRECTORIES "${_mpfr_library_dir}"
        INTERFACE_LINK_LIBRARIES "mpfr;GMP::gmp"
    )
  endif()

  unset(_mpfr_library_dir)
endif()
