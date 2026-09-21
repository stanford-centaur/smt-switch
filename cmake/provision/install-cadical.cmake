# Installs CaDiCaL, which has no install target of its own.
#
# Run with cmake -P and -DSOURCE_DIR=... -DINSTALL_DIR=...  The layout is the
# one cmake/FindCaDiCaL.cmake looks for, and it is not CaDiCaL's own: Bitwuzla
# expects cadical/cadical.hpp while Boolector expects ccadical.h at the top,
# so the two headers land in different places.

foreach(_required SOURCE_DIR INSTALL_DIR)
  if(NOT ${_required})
    message(FATAL_ERROR "install-cadical.cmake requires -D${_required}=<path>")
  endif()
endforeach()

file(INSTALL "${SOURCE_DIR}/src/ccadical.h" DESTINATION "${INSTALL_DIR}/include")
file(
  INSTALL "${SOURCE_DIR}/src/cadical.hpp" "${SOURCE_DIR}/src/tracer.hpp"
  DESTINATION "${INSTALL_DIR}/include/cadical"
)
file(INSTALL "${SOURCE_DIR}/build/libcadical.a" DESTINATION "${INSTALL_DIR}/lib")
