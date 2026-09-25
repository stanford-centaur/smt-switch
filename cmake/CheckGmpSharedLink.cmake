#[=======================================================================[.rst:
CheckGmpSharedLink
------------------

Decides whether GMP can be linked into a shared library.

.. command:: smt_switch_check_gmp_shared_link

  .. code-block:: cmake

    smt_switch_check_gmp_shared_link(<output> <component>...)

  Sets ``<output>`` to whether a shared library may link the named GMP
  components.  A distribution that ships ``libgmp.so`` can always do so; one
  that ships only ``libgmp.a`` can only if that archive was built position
  independent, which Debian's and Ubuntu's are not.

  The answer is not the same as whether GMP was found, and not the same as
  whether an *executable* may link it: an archive built for executables alone
  links into them perfectly well.  So a caller that can produce an archive
  instead should do that, and only a caller that must have a shared object --
  a Python extension module, or a shared ``smt-switch`` -- should treat a
  false answer as fatal.

#]=======================================================================]

include_guard(GLOBAL)

function(smt_switch_check_gmp_shared_link output)
  set(components ${ARGN})
  list(GET components -1 top_component)

  if(DEFINED SMT_SWITCH_GMP_LINKS_SHARED)
    set(${output} "${SMT_SWITCH_GMP_LINKS_SHARED}" PARENT_SCOPE)
    return()
  endif()

  # A shared GMP settles it, and is what every distribution we know of ships:
  # Debian, Ubuntu and Homebrew carry both forms, Arch only this one. The
  # archive probe below is the rare branch.
  set(saved_suffixes "${CMAKE_FIND_LIBRARY_SUFFIXES}")
  set(CMAKE_FIND_LIBRARY_SUFFIXES "${CMAKE_SHARED_LIBRARY_SUFFIX}")
  find_library(SMT_SWITCH_GMP_SHARED_LIBRARY NAMES gmp)
  set(CMAKE_FIND_LIBRARY_SUFFIXES "${saved_suffixes}")
  mark_as_advanced(SMT_SWITCH_GMP_SHARED_LIBRARY)

  if(SMT_SWITCH_GMP_SHARED_LIBRARY)
    set(answer TRUE)
    set(reason "a shared GMP is installed")
  else()
    message(STATUS "Checking whether GMP's archive can go into a shared library")
    try_compile(
      answer
      "${CMAKE_CURRENT_BINARY_DIR}/CMakeFiles/gmp-shared"
      "${CMAKE_CURRENT_LIST_DIR}/checks/gmp-shared"
      gmp-shared
      CMAKE_FLAGS
        "-DGMP_CHECK_MODULE_PATH=${CMAKE_CURRENT_LIST_DIR}"
        "-DGMP_CHECK_COMPONENTS=${components}"
        "-DGMP_CHECK_TOP_COMPONENT=${top_component}"
    )
    if(answer)
      set(reason "its archive is position independent")
    else()
      set(reason "its archive is not position independent")
    endif()
  endif()

  set(
    SMT_SWITCH_GMP_LINKS_SHARED
    "${answer}"
    CACHE INTERNAL
    "Whether a shared library may link GMP"
  )
  message(STATUS "GMP in a shared library: ${answer} (${reason})")
  set(${output} "${answer}" PARENT_SCOPE)
endfunction()
