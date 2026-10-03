# Yices2 looks for GMP with `cc -lgmp`, which does not find the GMP installed
# by Homebrew on macOS, so we need to add its headers and libraries manually
# to the compiler search paths.
find_package(GMP QUIET)
set(YICES2_ENV "")
if(GMP_FOUND)
  smt_switch_prepend_path(CPATH "${GMP_INCLUDE_DIRS}" YICES2_CPATH)
  smt_switch_prepend_path(LIBRARY_PATH "${GMP_LIBRARY_DIRS}" YICES2_LIBRARY_PATH)
  set(
    YICES2_ENV
    "${CMAKE_COMMAND}"
    -E
    env
    "${YICES2_CPATH}"
    "${YICES2_LIBRARY_PATH}"
  )
endif()

smt_switch_dependency(
  yices2
  URL "${YICES2_URL}"
  # Yices2 uses Autotools, but the release archive carries no configure
  # script, so autoconf runs first.
  CONFIGURE_COMMAND autoconf
  COMMAND ${YICES2_ENV} <SOURCE_DIR>/configure --enable-thread-safety --prefix=<INSTALL_DIR>
  BUILD_COMMAND ${YICES2_ENV} make build_dir=build BUILD=build -j${SMT_SWITCH_DEPS_JOBS}
  # LDCONFIG lives in /usr/sbin, which is not always on a user's PATH, and all
  # it would do is refresh symlinks next to the staged library.
  INSTALL_COMMAND make build_dir=build BUILD=build prefix=<INSTALL_DIR> LDCONFIG=true install
  BUILD_IN_SOURCE TRUE
)
