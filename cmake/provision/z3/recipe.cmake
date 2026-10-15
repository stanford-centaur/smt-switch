# Z3 requires a newer CMake than smt-switch does. Without this check the
# archive is downloaded before Z3's own configure step refuses.
if("z3" IN_LIST _requested AND CMAKE_VERSION VERSION_LESS 3.26)
  message(
    FATAL_ERROR
    "Building Z3 requires CMake 3.26 or later, but this is CMake "
    "${CMAKE_VERSION}. Upgrade CMake, or install Z3 yourself and point "
    "--z3-dir at it."
  )
endif()

# Z3 declares LANGUAGES CXX, so the C compiler we forward everywhere else
# goes unused here and CMake reports it.
set(Z3_CMAKE_ARGS ${COMMON_CMAKE_ARGS})
list(FILTER Z3_CMAKE_ARGS EXCLUDE REGEX "^-DCMAKE_C_COMPILER")

smt_switch_dependency(
  z3
  URL "${Z3_URL}"
  CMAKE_ARGS
    ${Z3_CMAKE_ARGS}
    -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
    # Z3 would run git inside our checkout and stamp our commit as its own.
    -DZ3_INCLUDE_GIT_DESCRIBE=OFF
    -DZ3_INCLUDE_GIT_HASH=OFF
  BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> -j${SMT_SWITCH_DEPS_JOBS}
)
