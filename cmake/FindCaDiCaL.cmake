#[=======================================================================[.rst:
FindCaDiCaL
-----------

Finds the CaDiCaL SAT solver.

CaDiCaL has no install target of its own, so ``cmake/provision/`` lays out the
headers and the archive itself.  This module looks for that layout, and for a
CaDiCaL installed anywhere else the same way.

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported target, if found:

``CaDiCaL::cadical``
  The CaDiCaL library.

The target carries both an ``IMPORTED_LOCATION`` and an
``INTERFACE_LINK_DIRECTORIES`` entry, on purpose.  The location is what puts
the archive itself on the link line of a target that links this one, such as
``smt-switch-cvc5``.  The link directory is for the other consumer: the cvc5
CMake package lists ``cadical`` as a plain library name in its link interface,
so the directory holding it has to reach the link line even when nothing
mentions this target's file.

Result Variables
^^^^^^^^^^^^^^^^

``CaDiCaL_FOUND``
  Boolean indicating whether CaDiCaL was found.
``CaDiCaL_INCLUDE_DIRS``
  The include directories of CaDiCaL.
``CaDiCaL_LIBRARIES``
  The CaDiCaL library.

Cache Variables
^^^^^^^^^^^^^^^

``CaDiCaL_INCLUDE_DIR``
  The directory containing ``ccadical.h``.
``CaDiCaL_LIBRARY``
  The path to the CaDiCaL library.

#]=======================================================================]

find_path(CaDiCaL_INCLUDE_DIR NAMES ccadical.h)
find_library(CaDiCaL_LIBRARY NAMES cadical)
mark_as_advanced(CaDiCaL_INCLUDE_DIR CaDiCaL_LIBRARY)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(CaDiCaL REQUIRED_VARS CaDiCaL_LIBRARY CaDiCaL_INCLUDE_DIR)

if(CaDiCaL_FOUND)
  set(CaDiCaL_INCLUDE_DIRS "${CaDiCaL_INCLUDE_DIR}")
  set(CaDiCaL_LIBRARIES "${CaDiCaL_LIBRARY}")

  if(NOT TARGET CaDiCaL::cadical)
    get_filename_component(_cadical_library_dir "${CaDiCaL_LIBRARY}" DIRECTORY)
    add_library(CaDiCaL::cadical UNKNOWN IMPORTED GLOBAL)
    set_target_properties(
      CaDiCaL::cadical
      PROPERTIES
        IMPORTED_LOCATION "${CaDiCaL_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${CaDiCaL_INCLUDE_DIR}"
        INTERFACE_LINK_DIRECTORIES "${_cadical_library_dir}"
    )
    unset(_cadical_library_dir)
  endif()
endif()
