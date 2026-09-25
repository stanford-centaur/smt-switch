#[=======================================================================[.rst:
FindMathSAT
-----------

Finds the MathSAT5 SMT solver.

MathSAT is distributed as a prebuilt archive with no CMake package and no
pkg-config file, so this module looks for the header and the library
directly.  It is never downloaded automatically; the MathSAT section of the
README says how to obtain it.

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported target, if found:

``MathSAT::mathsat``
  The MathSAT5 library.

MathSAT is built against GMP but does not say so anywhere a build system can
read, so a consumer has to link :module:`FindGMP`'s ``GMP::gmp`` alongside
this target.

Result Variables
^^^^^^^^^^^^^^^^

``MathSAT_FOUND``
  Boolean indicating whether MathSAT was found.
``MathSAT_INCLUDE_DIRS``
  The include directories of MathSAT.
``MathSAT_LIBRARIES``
  The MathSAT library.

Cache Variables
^^^^^^^^^^^^^^^

``MathSAT_INCLUDE_DIR``
  The directory containing ``mathsat.h``.
``MathSAT_LIBRARY``
  The path to the MathSAT library.

#]=======================================================================]

find_path(MathSAT_INCLUDE_DIR NAMES mathsat.h)
find_library(MathSAT_LIBRARY NAMES mathsat)
mark_as_advanced(MathSAT_INCLUDE_DIR MathSAT_LIBRARY)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(MathSAT REQUIRED_VARS MathSAT_LIBRARY MathSAT_INCLUDE_DIR)

if(MathSAT_FOUND)
  set(MathSAT_INCLUDE_DIRS "${MathSAT_INCLUDE_DIR}")
  set(MathSAT_LIBRARIES "${MathSAT_LIBRARY}")

  if(NOT TARGET MathSAT::mathsat)
    add_library(MathSAT::mathsat UNKNOWN IMPORTED GLOBAL)
    set_target_properties(
      MathSAT::mathsat
      PROPERTIES
        IMPORTED_LOCATION "${MathSAT_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${MathSAT_INCLUDE_DIR}"
    )
  endif()
endif()
