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

Result Variables
^^^^^^^^^^^^^^^^

``Yices2_FOUND``
  Boolean indicating whether Yices2 was found.
``Yices2_INCLUDE_DIRS``
  The include directories of Yices2.
``Yices2_LIBRARIES``
  The Yices2 library.

Cache Variables
^^^^^^^^^^^^^^^

``Yices2_INCLUDE_DIR``
  The directory containing ``yices.h``.
``Yices2_LIBRARY``
  The path to the Yices2 library.

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

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Yices2 REQUIRED_VARS Yices2_LIBRARY Yices2_INCLUDE_DIR)

if(Yices2_FOUND)
  set(Yices2_INCLUDE_DIRS "${Yices2_INCLUDE_DIR}")
  set(Yices2_LIBRARIES "${Yices2_LIBRARY}")

  if(NOT TARGET Yices2::yices)
    find_package(Threads REQUIRED)
    add_library(Yices2::yices UNKNOWN IMPORTED GLOBAL)
    set_target_properties(
      Yices2::yices
      PROPERTIES
        IMPORTED_LOCATION "${Yices2_LIBRARY}"
        INTERFACE_INCLUDE_DIRECTORIES "${Yices2_INCLUDE_DIR}"
    )
    target_link_libraries(Yices2::yices INTERFACE Threads::Threads)
  endif()
endif()
