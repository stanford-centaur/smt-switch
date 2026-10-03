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
    -DZ3_BUILD_LIBZ3_SHARED=OFF
    # The git options default to on but there is no .git in a release tarball.
    -DZ3_INCLUDE_GIT_DESCRIBE=OFF
    -DZ3_INCLUDE_GIT_HASH=OFF
  BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> -j${SMT_SWITCH_DEPS_JOBS}
)
