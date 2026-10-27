# Commands shared across the build's CMake code.
#
# gersemi is pointed at this file, so a command defined here is formatted at
# its call sites rather than left however it was typed. That works when the
# definition takes its arguments through cmake_parse_arguments, which is a
# reason to prefer writing them that way; a command taking positional
# arguments gains nothing from being moved here.

include_guard(GLOBAL)

# Sets <output> to whatever <macro> is defined to in <header> of the install
# that <library> belongs to, without the quotes if it is a string, or to
# "unknown" if that cannot be read. The header sits beside lib/ or, in a multiarch
# layout, beside lib/<arch>/; never one found elsewhere.
function(_smt_switch_library_version library header macro output)
  get_filename_component(library_dir "${library}" DIRECTORY)
  unset(_smt_switch_include_dir CACHE)
  find_path(
    _smt_switch_include_dir
    NAMES "${header}"
    PATHS "${library_dir}/.." "${library_dir}/../.."
    PATH_SUFFIXES include
    NO_DEFAULT_PATH
  )
  set(version "")
  if(_smt_switch_include_dir)
    set(define "^#define[\t ]+${macro}[\t ]+(\"([^\"]*)\"|([^\t ]+))")
    # without an encoding, any byte outside printable ASCII ends a line
    file(STRINGS "${_smt_switch_include_dir}/${header}" lines REGEX "${define}" ENCODING UTF-8)
    if(lines)
      list(GET lines 0 line)
      string(REGEX MATCH "${define}" match "${line}")
      set(version "${CMAKE_MATCH_2}${CMAKE_MATCH_3}")
    endif()
  endif()
  if(NOT version)
    set(version "unknown")
  endif()
  unset(_smt_switch_include_dir CACHE)
  set(${output} "${version}" PARENT_SCOPE)
endfunction()

# Checks that the libraries the variables <var> and <other-var> hold are the
# same version of the library NAME, as read from the VERSION_MACRO in its
# HEADER. When two copies of a library without namespaced symbols are
# linked, one of them serves both users, which is only safe if they are the
# same version. So configure fails if they are not, and warns if either
# version cannot be read. Nothing is checked if both are the same file.
function(smt_switch_check_library_versions var other_var)
  cmake_parse_arguments(CHECK "" "NAME;HEADER;VERSION_MACRO" "" ${ARGN})
  if(NOT CHECK_NAME OR NOT CHECK_HEADER OR NOT CHECK_VERSION_MACRO)
    message(FATAL_ERROR "smt_switch_check_library_versions needs NAME, HEADER and VERSION_MACRO")
  endif()
  set(library "${${var}}")
  set(other_library "${${other_var}}")
  if(library STREQUAL other_library)
    return()
  endif()
  _smt_switch_library_version("${library}" "${CHECK_HEADER}" "${CHECK_VERSION_MACRO}" version)
  _smt_switch_library_version(
    "${other_library}"
    "${CHECK_HEADER}"
    "${CHECK_VERSION_MACRO}"
    other_version
  )
  string(
    CONCAT libraries
    "${var} is ${library} (${CHECK_NAME} ${version}) and ${other_var} is "
    "${other_library} (${CHECK_NAME} ${other_version})"
  )
  if(version STREQUAL "unknown" OR other_version STREQUAL "unknown")
    message(WARNING "${libraries}. Only one is linked, so make sure they are the same version.")
  elseif(NOT version STREQUAL other_version)
    message(
      FATAL_ERROR
      "${libraries}. Only one is linked, so they must be the same version: "
      "point ${var} at the ${CHECK_NAME} of ${other_var}, or build both against "
      "one ${CHECK_NAME}."
    )
  endif()
endfunction()

# Sets the cache variable <var> to whether the C++ SOURCE compiles against
# the headers of the imported TARGETS, without linking anything. It is
# checked afresh on every configure, so pointing the build at another install
# of a library is noticed.
function(smt_switch_check_source_compiles var)
  cmake_parse_arguments(PARSE_ARGV 1 CHECK "" "SOURCE" "TARGETS")
  if(NOT CHECK_TARGETS OR NOT CHECK_SOURCE)
    message(FATAL_ERROR "smt_switch_check_source_compiles needs TARGETS and SOURCE")
  endif()
  include(CheckCXXSourceCompiles)
  include(CMakePushCheckState)
  cmake_push_check_state(RESET)
  set(CMAKE_REQUIRED_QUIET TRUE)
  set(CMAKE_REQUIRED_LIBRARIES ${CHECK_TARGETS})
  set(CMAKE_TRY_COMPILE_TARGET_TYPE STATIC_LIBRARY)
  unset(${var} CACHE)
  check_cxx_source_compiles("${CHECK_SOURCE}" ${var})
  cmake_pop_check_state()
endfunction()
