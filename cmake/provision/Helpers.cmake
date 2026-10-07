# Commands shared across the dependency provisioner's CMake code.
#
# gersemi is pointed at this file, so a command defined here is formatted at
# its call sites rather than left however it was typed. That works when the
# definition takes its arguments through cmake_parse_arguments, which is a
# reason to prefer writing them that way; a command taking positional
# arguments gains nothing from being moved here.

include_guard(GLOBAL)

# Captured here, as CMAKE_CURRENT_FUNCTION_LIST_DIR needs CMake 3.17
set(_smt_switch_provision_dir "${CMAKE_CURRENT_LIST_DIR}")

# Sets <output> to every pinned dependency, in order of name: the
# directories of cmake/provision that hold a pin.cmake. Each of them also
# needs a recipe.cmake, which the provisioning driver includes.
function(smt_switch_dependencies output)
  file(
    GLOB pins
    RELATIVE "${_smt_switch_provision_dir}"
    "${_smt_switch_provision_dir}/*/pin.cmake"
  )
  set(dependencies "")
  foreach(pin IN LISTS pins)
    get_filename_component(dependency "${pin}" DIRECTORY)
    list(APPEND dependencies "${dependency}")
  endforeach()
  set(${output} "${dependencies}" PARENT_SCOPE)
endfunction()

# Pinned versions of the dependencies this project can build for itself.
#
# Bumping one in a dependency's pin.cmake rebuilds that dependency and
# everything that depends on it: the URL is baked into the download script
# ExternalProject generates, and that script is a dependency of the download
# step.
#
# A pin says where the source comes from and what it must hash to, and
# nothing else: cmake/provision/CMakeLists.txt refuses to configure without
# a checksum, and recording one in the pin after a bump, or for a new pin,
# is
#
#   cmake -P cmake/provision/update-checksums.cmake <name>...
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
# a GitHub tag, a GitHub commit, or a GNU release tarball. A pin without a
# CHECKSUM leaves <name>_SHA256 empty rather than failing, so that
# update-checksums.cmake can still read it to add one.
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
  set(${name}_URL "${url}" PARENT_SCOPE)
  set(${name}_SHA256 "${PIN_CHECKSUM}" PARENT_SCOPE)
endfunction()
