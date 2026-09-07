#[=======================================================================[.rst:
FindGMP
-------

Finds the GNU Multiple Precision Arithmetic Library (GMP) and, optionally, its
C++ bindings.

Components
^^^^^^^^^^

``gmp``
  The C library, ``libgmp`` and ``gmp.h``.  Requested by default.
``gmpxx``
  The C++ bindings, ``libgmpxx`` and ``gmpxx.h``.  Requesting these implies
  ``gmp``, because ``libgmpxx`` is built on top of ``libgmp``::

    find_package(GMP REQUIRED COMPONENTS gmpxx)

Imported Targets
^^^^^^^^^^^^^^^^

This module provides the following imported targets, if found:

``GMP::gmp``
  The GMP C library.
``GMP::gmpxx``
  The GMP C++ bindings.  Depends on ``GMP::gmp``, so linking against this
  target alone is enough, and the two libraries reach the link line in an
  order that resolves.

Both targets name their library rather than pointing at the file that was
found, so that the linker picks the shared library or the static archive
depending on how the consumer is being linked.  An imported target with an
``IMPORTED_LOCATION`` would name ``libgmp.so`` by absolute path, which stays on
the link line even under ``-static``, leaving a dynamic dependency on GMP in
what was supposed to be a static binary.

Result Variables
^^^^^^^^^^^^^^^^

This module defines the following variables:

``GMP_FOUND``
  Boolean indicating whether GMP and every requested component were found.
``GMP_gmp_FOUND``, ``GMP_gmpxx_FOUND``
  Booleans indicating whether the individual components were found.
``GMP_INCLUDE_DIRS``
  The include directories of the requested components.
``GMP_LIBRARY_DIRS``
  The directories holding the libraries of the requested components.
``GMP_LINK_LIBRARIES``
  The names of the libraries of the requested components, in the order they
  have to be linked in.  Together with ``GMP_LIBRARY_DIRS`` this is what the
  imported targets above expand to; prefer the targets, and reach for these
  variables only where a target cannot be used, such as when handing the flags
  to a build system other than CMake.

Cache Variables
^^^^^^^^^^^^^^^

The following cache variables may also be set:

``GMP_INCLUDE_DIR``
  The directory containing ``gmp.h``.
``GMP_gmpxx_INCLUDE_DIR``
  The directory containing ``gmpxx.h``.  Not necessarily the directory above:
  Debian and its derivatives install ``gmp.h`` into the architecture-specific
  include directory, but not ``gmpxx.h``.
``GMP_gmp_LIBRARY``
  The path to the GMP C library.
``GMP_gmpxx_LIBRARY``
  The path to the GMP C++ bindings library.

#]=======================================================================]

# The C++ bindings cannot be used on their own: libgmpxx is built on top of
# libgmp, and gmpxx.h includes gmp.h. Requesting them therefore implies the C
# library, at the same level of requiredness.
if(NOT GMP_FIND_COMPONENTS)
  set(GMP_FIND_COMPONENTS gmp)
endif()
if("gmpxx" IN_LIST GMP_FIND_COMPONENTS AND NOT "gmp" IN_LIST GMP_FIND_COMPONENTS)
  list(APPEND GMP_FIND_COMPONENTS gmp)
  set(GMP_FIND_REQUIRED_gmp "${GMP_FIND_REQUIRED_gmpxx}")
endif()

find_path(GMP_INCLUDE_DIR NAMES gmp.h)
find_path(GMP_gmpxx_INCLUDE_DIR NAMES gmpxx.h)
find_library(GMP_gmp_LIBRARY NAMES gmp)
find_library(GMP_gmpxx_LIBRARY NAMES gmpxx)
mark_as_advanced(GMP_INCLUDE_DIR GMP_gmpxx_INCLUDE_DIR GMP_gmp_LIBRARY GMP_gmpxx_LIBRARY)

set(GMP_gmp_FOUND FALSE)
if(GMP_INCLUDE_DIR AND GMP_gmp_LIBRARY)
  set(GMP_gmp_FOUND TRUE)
endif()

set(GMP_gmpxx_FOUND FALSE)
if(GMP_gmp_FOUND AND GMP_gmpxx_INCLUDE_DIR AND GMP_gmpxx_LIBRARY)
  set(GMP_gmpxx_FOUND TRUE)
endif()

include(FindPackageHandleStandardArgs)
# The C library is required whichever components were asked for, because the
# expansion above adds it to every request that does not name it already.
find_package_handle_standard_args(
  GMP
  REQUIRED_VARS GMP_gmp_LIBRARY GMP_INCLUDE_DIR
  HANDLE_COMPONENTS
)

if(GMP_FOUND)
  get_filename_component(gmp_library_dir "${GMP_gmp_LIBRARY}" DIRECTORY)

  # Report what was requested rather than what happens to be installed, so
  # that a consumer of the C library alone does not end up linking libgmpxx.
  set(GMP_INCLUDE_DIRS "${GMP_INCLUDE_DIR}")
  set(GMP_LIBRARY_DIRS "${gmp_library_dir}")
  set(GMP_LINK_LIBRARIES gmp)

  # Name the library instead of the file that was found. This is the whole
  # point of the module: -lgmp lets a static link substitute libgmp.a, and
  # CMake still derives the rpath from the link directory, so a GMP outside
  # the system prefix is found at run time all the same.
  if(NOT TARGET GMP::gmp)
    add_library(GMP::gmp INTERFACE IMPORTED GLOBAL)
    set_target_properties(
      GMP::gmp
      PROPERTIES
        INTERFACE_INCLUDE_DIRECTORIES "${GMP_INCLUDE_DIR}"
        INTERFACE_LINK_DIRECTORIES "${gmp_library_dir}"
        INTERFACE_LINK_LIBRARIES gmp
    )
  endif()

  if(GMP_gmpxx_FOUND)
    get_filename_component(gmpxx_library_dir "${GMP_gmpxx_LIBRARY}" DIRECTORY)

    if("gmpxx" IN_LIST GMP_FIND_COMPONENTS)
      list(APPEND GMP_INCLUDE_DIRS "${GMP_gmpxx_INCLUDE_DIR}")
      list(APPEND GMP_LIBRARY_DIRS "${gmpxx_library_dir}")
      list(REMOVE_DUPLICATES GMP_INCLUDE_DIRS)
      list(REMOVE_DUPLICATES GMP_LIBRARY_DIRS)
      # libgmpxx has to be linked before libgmp: it references symbols from
      # the C library, and an archive only resolves what is undefined by the
      # time the linker reaches it.
      set(GMP_LINK_LIBRARIES gmpxx gmp)
    endif()

    # Created whenever the C++ bindings are installed, even if they were not
    # requested here, so that another directory may link them without asking
    # again. Linking a target that does not exist is a configure-time error,
    # never a silent misbuild.
    if(NOT TARGET GMP::gmpxx)
      add_library(GMP::gmpxx INTERFACE IMPORTED GLOBAL)
      set_target_properties(
        GMP::gmpxx
        PROPERTIES
          INTERFACE_INCLUDE_DIRECTORIES "${GMP_gmpxx_INCLUDE_DIR}"
          INTERFACE_LINK_DIRECTORIES "${gmpxx_library_dir}"
          INTERFACE_LINK_LIBRARIES "gmpxx;GMP::gmp"
      )
    endif()
  endif()
endif()
