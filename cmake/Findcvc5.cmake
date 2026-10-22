#[=======================================================================[.rst:
Findcvc5
--------

Finds the cvc5 SMT solver through its own CMake package, and adds what that
package leaves out.

cvc5's package names the CaDiCaL and LibPoly (``picpoly`` and ``picpolyxx``)
it links in the link interface of ``cvc5::cvc5`` by bare library name, and
records nowhere where they are, so a link against ``cvc5::cvc5`` alone cannot
find them.  This module loads the package, finds the three libraries, beside
the cvc5 library before anywhere else, as that is where they sit when cvc5
built them, and adds their directories to the link interface of
``cvc5::cvc5``.  The names stay names, so that the linker still picks a
shared library or a static archive for each link: a program linked with
``-static`` and a shared object built beside it each get the kind they need.

A requested version is a minimum, as for any package, or an exact match with
``EXACT``.  cvc5's own package accepts only an exact match, so it is asked
for no version, and the version it reports is compared here.

Imported Targets
^^^^^^^^^^^^^^^^

``cvc5::cvc5``
  cvc5's own target, with the directories above added.

Result Variables
^^^^^^^^^^^^^^^^

``cvc5_FOUND``
  Boolean indicating whether cvc5 and the libraries it links were found.
``cvc5_VERSION``
  The version cvc5's package reports.

Cache Variables
^^^^^^^^^^^^^^^

``cvc5_DIR``
  The directory containing cvc5's package configuration file.
``cvc5_CADICAL_LIBRARY``, ``cvc5_POLY_LIBRARY``, ``cvc5_POLYXX_LIBRARY``
  The CaDiCaL, ``picpoly`` and ``picpolyxx`` libraries cvc5 links.

#]=======================================================================]

# A find_package from within a find module takes the version asked of the
# module when it names none, and cvc5_FIND_MODULE is what marks it as being
# from within one, so that is cleared while the package is loaded.
set(_cvc5_find_module "${cvc5_FIND_MODULE}")
unset(cvc5_FIND_MODULE)
find_package(cvc5 CONFIG QUIET)
set(cvc5_FIND_MODULE "${_cvc5_find_module}")

set(_cvc5_library_dirs "")
if(TARGET cvc5::cvc5)
  # The cvc5 library itself, read off the imported target as a plain path:
  # $<TARGET_FILE:...> is a generator expression, and find_library runs
  # before generation. cvc5 exports only its PRODUCTION configuration, which
  # need not be the one being built, so the first exported configuration is
  # taken when the build's own is missing.
  get_target_property(_cvc5_library cvc5::cvc5 IMPORTED_LOCATION)
  if(NOT _cvc5_library)
    get_target_property(_cvc5_configurations cvc5::cvc5 IMPORTED_CONFIGURATIONS)
    if(_cvc5_configurations)
      string(TOUPPER "${CMAKE_BUILD_TYPE}" _cvc5_build_type)
      if(NOT _cvc5_build_type IN_LIST _cvc5_configurations)
        list(GET _cvc5_configurations 0 _cvc5_build_type)
      endif()
      get_target_property(_cvc5_library cvc5::cvc5 IMPORTED_LOCATION_${_cvc5_build_type})
    endif()
  endif()
  get_filename_component(_cvc5_library_dir "${_cvc5_library}" DIRECTORY)

  # The variables call LibPoly's position-independent build just POLY.
  foreach(_cvc5_name IN ITEMS cadical picpoly picpolyxx)
    string(TOUPPER "${_cvc5_name}" _cvc5_var)
    string(REPLACE "PIC" "" _cvc5_var "cvc5_${_cvc5_var}_LIBRARY")
    find_library(${_cvc5_var} NAMES "${_cvc5_name}" HINTS "${_cvc5_library_dir}")
    mark_as_advanced(${_cvc5_var})
    if(${_cvc5_var})
      get_filename_component(_cvc5_dir "${${_cvc5_var}}" DIRECTORY)
      list(APPEND _cvc5_library_dirs "${_cvc5_dir}")
    endif()
  endforeach()
  list(REMOVE_DUPLICATES _cvc5_library_dirs)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(
  cvc5
  REQUIRED_VARS cvc5_CONFIG cvc5_CADICAL_LIBRARY cvc5_POLY_LIBRARY cvc5_POLYXX_LIBRARY
  VERSION_VAR cvc5_VERSION
)

# The directories go in as -L flags as well, which reach a consumer that links
# cvc5::cvc5 as the private dependency of a static library, through
# $<LINK_ONLY:>, where link directories do not. Each only once, however often
# cvc5 is looked for, as its package defines the target only the first time.
if(cvc5_FOUND)
  get_target_property(_cvc5_link_dirs cvc5::cvc5 INTERFACE_LINK_DIRECTORIES)
  foreach(_cvc5_dir IN LISTS _cvc5_library_dirs)
    if(NOT _cvc5_dir IN_LIST _cvc5_link_dirs)
      set_property(TARGET cvc5::cvc5 APPEND PROPERTY INTERFACE_LINK_DIRECTORIES "${_cvc5_dir}")
      set_property(TARGET cvc5::cvc5 APPEND PROPERTY INTERFACE_LINK_LIBRARIES "-L${_cvc5_dir}")
    endif()
  endforeach()
endif()

unset(_cvc5_build_type)
unset(_cvc5_configurations)
unset(_cvc5_dir)
unset(_cvc5_find_module)
unset(_cvc5_library)
unset(_cvc5_library_dir)
unset(_cvc5_library_dirs)
unset(_cvc5_link_dirs)
unset(_cvc5_name)
unset(_cvc5_var)
