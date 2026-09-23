# Commands shared across this project's CMake code.
#
# gersemi is pointed at this file, so a command defined here is formatted at
# its call sites rather than left however it was typed. That works when the
# definition takes its arguments through cmake_parse_arguments, which is a
# reason to prefer writing them that way; a command taking positional
# arguments gains nothing from being moved here. The project has several
# others that gersemi still reports as unknown, and they can move here as
# and when they are worth the change.

include_guard(GLOBAL)

# Sets <name>_URL and <name>_SHA256 from one of three kinds of source:
# a GitHub tag, a GitHub commit, or a GNU release tarball.
function(smt_switch_pin name)
  cmake_parse_arguments(PIN "" "GITHUB_REPO;TAG;COMMIT;GNU_PROJECT;VERSION;CHECKSUM" "" ${ARGN})
  if(PIN_GITHUB_REPO AND PIN_TAG)
    set(url "https://github.com/${PIN_GITHUB_REPO}/archive/refs/tags/${PIN_TAG}.tar.gz")
  elseif(PIN_GITHUB_REPO AND PIN_COMMIT)
    set(url "https://github.com/${PIN_GITHUB_REPO}/archive/${PIN_COMMIT}.tar.gz")
  elseif(PIN_GNU_PROJECT AND PIN_VERSION)
    set(mirror "https://mirror.us-midwest-1.nexcess.net/gnu")
    set(url "${mirror}/${PIN_GNU_PROJECT}/${PIN_GNU_PROJECT}-${PIN_VERSION}.tar.gz")
  else()
    message(FATAL_ERROR "${name} names no source to download")
  endif()
  if(NOT PIN_CHECKSUM)
    message(FATAL_ERROR "${name} has no CHECKSUM")
  endif()
  set(${name}_URL "${url}" PARENT_SCOPE)
  set(${name}_SHA256 "${PIN_CHECKSUM}" PARENT_SCOPE)
endfunction()
