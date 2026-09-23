# Prints the SHA-256 of every pinned download, ready to paste into
# versions.cmake, and says which ones no longer match what is recorded there.
#
#   cmake -P cmake/provision/refresh-hashes.cmake            # every pin
#   cmake -P cmake/provision/refresh-hashes.cmake z3 cvc5    # just these
#
# Run it after bumping a pin, and to answer the question of whether a
# verification failure is a bumped URL or something worse.

cmake_minimum_required(VERSION 3.14)

# The downloads this script makes deserve the same treatment as the ones the
# driver makes; see the note on CMAKE_TLS_VERIFY in CMakeLists.txt.
set(CMAKE_TLS_VERIFY TRUE)

include("${CMAKE_CURRENT_LIST_DIR}/versions.cmake")

set(
  _all_dependencies
  cadical
  btor2tools
  boolector
  bitwuzla
  cvc5
  z3
  yices2
  bison
)

# Anything after the script name selects a subset, so that bumping one pin
# does not mean downloading the other seven.
set(_requested "")
if(CMAKE_ARGC GREATER 3)
  math(EXPR _last "${CMAKE_ARGC} - 1")
  foreach(_index RANGE 3 ${_last})
    list(APPEND _requested "${CMAKE_ARGV${_index}}")
  endforeach()
endif()
if(NOT _requested)
  set(_requested ${_all_dependencies})
endif()

foreach(_dependency IN LISTS _requested)
  if(NOT _dependency IN_LIST _all_dependencies)
    message(FATAL_ERROR "There is no pin named '${_dependency}'")
  endif()
endforeach()

set(_scratch "${CMAKE_CURRENT_BINARY_DIR}/.refresh-hashes")
file(MAKE_DIRECTORY "${_scratch}")

set(_differs "")
foreach(_dependency IN LISTS _requested)
  string(TOUPPER "${_dependency}" _upper)
  set(_url "${${_upper}_URL}")
  set(_recorded "${${_upper}_SHA256}")

  message(STATUS "Fetching ${_dependency} from ${_url}")
  set(_archive "${_scratch}/${_dependency}")
  file(DOWNLOAD "${_url}" "${_archive}" STATUS _status)
  list(GET _status 0 _code)
  if(NOT _code EQUAL 0)
    list(GET _status 1 _reason)
    message(FATAL_ERROR "Could not fetch ${_url}: ${_reason}")
  endif()
  file(SHA256 "${_archive}" _hash)
  file(REMOVE "${_archive}")

  message("set(${_upper}_SHA256 ${_hash})")
  if(_recorded AND NOT _recorded STREQUAL _hash)
    list(APPEND _differs "${_dependency}")
  endif()
endforeach()

file(REMOVE_RECURSE "${_scratch}")

if(_differs)
  list(JOIN _differs ", " _names)
  message(
    FATAL_ERROR
    "Recorded hash no longer matches what the URL serves: ${_names}. A "
    "bumped pin explains one; all of the GitHub ones at once is more likely "
    "to be GitHub regenerating its archives, which it does not promise to "
    "do reproducibly."
  )
endif()
