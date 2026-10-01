# Installs Boolector's CaDiCaL, which has no install target of its own.
#
# Run with cmake -P and -DSOURCE_DIR=... -DINSTALL_DIR=...  The layout is the
# one cmake/FindCaDiCaL.cmake looks for. Only the C header is installed: the
# C++ names in this archive are renamed (see CMakeLists.txt), so code built
# against cadical.hpp would not link against it.

foreach(_required SOURCE_DIR INSTALL_DIR)
  if(NOT ${_required})
    message(FATAL_ERROR "install-cadical.cmake requires -D${_required}=<path>")
  endif()
endforeach()

file(INSTALL "${SOURCE_DIR}/src/ccadical.h" DESTINATION "${INSTALL_DIR}/include")
file(INSTALL "${SOURCE_DIR}/build/libcadical.a" DESTINATION "${INSTALL_DIR}/lib")
