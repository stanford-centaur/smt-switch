# Commands shared across the dependency provisioner's CMake code.
#
# gersemi is pointed at this file, so a command defined here is formatted at
# its call sites rather than left however it was typed. That works when the
# definition takes its arguments through cmake_parse_arguments, which is a
# reason to prefer writing them that way; a command taking positional
# arguments gains nothing from being moved here.

include_guard(GLOBAL)

# Pinned versions of the dependencies this project can build for itself.
#
# Bumping one in a dependency's pin.cmake rebuilds that dependency and
# everything that depends on it: the URL is baked into the download script
# ExternalProject generates, and that script is a dependency of the download
# step.
#
# A pin says where the source comes from and what it must hash to, and
# nothing else: cmake/provision/CMakeLists.txt refuses to configure without
# a checksum, and recomputing one after a bump is
#
#   cmake -P cmake/provision/refresh-hashes.cmake <name>...
#
# Tags are preferred to commits, being self-describing. If one is ever moved
# the checksum catches it, because the archive changes and the download
# fails.
#
# Note that a GitHub /archive/ URL is generated on request rather than
# stored. GitHub guarantees the bytes only for assets a project uploads
# itself, which none of these publish, and has promised six months' notice
# before changing the archive format again. So if every GitHub pin fails
# verification at once, suspect that rather than five bad downloads.
#
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
