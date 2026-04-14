#[=======================================================================[.rst:
FindMathSAT
-------

Finds the MathSAT library.

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported targets, if found:

``MathSAT::MathSAT``
The MathSAT library

Result Variables
^^^^^^^^^^^^^^^^

This module defines the following variables:

``MathSAT_FOUND``
  Boolean indicating whether MathSAT was found.

Cache Variables
^^^^^^^^^^^^^^^

The following cache variables may also be set:

``MathSAT_INCLUDE_DIR``
  The directory containing ``mathsat.h``.
``MathSAT_LIBRARY``
  The path to the MathSAT library.

#]=======================================================================]
# MathSAT header and library files.
find_path(MathSAT_INCLUDE_DIR NAMES mathsat.h)
find_library(MathSAT_LIBRARIES NAMES mathsat)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(MathSAT DEFAULT_MSG MathSAT_INCLUDE_DIR MathSAT_LIBRARIES)
mark_as_advanced(MathSAT_INCLUDE_DIR MathSAT_LIBRARIES)
if(MathSAT_FOUND AND NOT TARGET MathSAT::MathSAT)
  # Find GMP dependency.
  find_package(PkgConfig REQUIRED)
  pkg_search_modules(GMP QUIET IMPORTED_TARGET gmp)
  if(NOT TARGET PkgConfig::GMP)
    message(FATAL_ERROR "GMP not found (required by MathSAT)")
  endif()
  # Create imported target.
  if(NOT TARGET MathSAT::MathSAT)
    add_library(MathSAT::MathSAT UNKNOWN IMPORTED)
    set_target_properties(
      MathSAT::MathSAT
      IMPORTED_LOCATION
      "${MathSAT_LIBRARY}"
      INTERFACE_INCLUDE_DIRECTORIES
      "${MathSAT_INCLUDE_DIR}"
    )
    target_link_libraries(MathSAT::MathSAT PRIVATE PkgConfig::GMP)
  endif()
endif()
