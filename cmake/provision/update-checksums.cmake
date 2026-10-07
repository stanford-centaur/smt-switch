# Downloads each pinned source and records its SHA-256 as the CHECKSUM in
# the dependency's pin.cmake, adding one to a pin that has none yet.
#
#   cmake -P cmake/provision/update-checksums.cmake            # every pin
#   cmake -P cmake/provision/update-checksums.cmake z3 cvc5    # just these
#
# Run it after bumping or adding a pin, then review the diff: a checksum
# that changed for a pin nobody bumped means the URL now serves something
# else.

cmake_minimum_required(VERSION 3.16)

# The downloads this script makes deserve the same treatment as the ones the
# driver makes; see the note on CMAKE_TLS_VERIFY in CMakeLists.txt.
set(CMAKE_TLS_VERIFY TRUE)

include("${CMAKE_CURRENT_LIST_DIR}/Helpers.cmake")
smt_switch_dependencies(_all_dependencies)
foreach(_dependency IN LISTS _all_dependencies)
  include("${CMAKE_CURRENT_LIST_DIR}/${_dependency}/pin.cmake")
endforeach()

# Anything after the script name selects a subset, so that bumping one pin
# does not mean downloading all the others.
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

set(_scratch "${CMAKE_CURRENT_BINARY_DIR}/.update-checksums")
file(MAKE_DIRECTORY "${_scratch}")

set(_changed "")
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

  if(_recorded STREQUAL _hash)
    message(STATUS "${_dependency}'s CHECKSUM is unchanged")
    continue()
  endif()

  # The pin is one smt_switch_pin call, so a missing CHECKSUM goes last in
  # it, just before the closing parenthesis on its own line.
  set(_pin "${CMAKE_CURRENT_LIST_DIR}/${_dependency}/pin.cmake")
  file(READ "${_pin}" _old_text)
  if(_recorded)
    string(REPLACE "CHECKSUM ${_recorded}" "CHECKSUM ${_hash}" _new_text "${_old_text}")
  else()
    string(REGEX REPLACE "\n\\)" "\n  CHECKSUM ${_hash}\n)" _new_text "${_old_text}")
  endif()
  if(_new_text STREQUAL _old_text)
    message(FATAL_ERROR "Could not find where to record the CHECKSUM in ${_pin}")
  endif()
  file(WRITE "${_pin}" "${_new_text}")
  message(STATUS "Recorded ${_dependency}'s CHECKSUM ${_hash}")
  if(_recorded)
    list(APPEND _changed "${_dependency}")
  endif()
endforeach()

file(REMOVE_RECURSE "${_scratch}")

if(_changed)
  list(JOIN _changed ", " _names)
  message(
    WARNING
    "Changed the recorded checksum of: ${_names}. A bumped pin explains "
    "one; all of the GitHub ones at once is more likely to be GitHub "
    "regenerating its archives, which it does not promise to do "
    "reproducibly."
  )
endif()
