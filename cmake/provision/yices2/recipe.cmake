# Yices2 looks for GMP with `cc -lgmp`, which does not find the GMP installed
# by Homebrew on macOS, so we need to add its headers and libraries manually
# to the compiler search paths.
find_package(GMP QUIET)
set(_yices2_include_dirs "")
set(_yices2_library_dirs "")
if(GMP_FOUND)
  list(APPEND _yices2_include_dirs ${GMP_INCLUDE_DIRS})
  list(APPEND _yices2_library_dirs ${GMP_LIBRARY_DIRS})
endif()

# MCSAT, which Yices2 needs for nonlinear arithmetic, requires LibPoly and
# CUDD. We do not provision either, so Yices2 gets MCSAT only when both are
# installed already, and is built without it otherwise.
find_path(YICES2_POLY_INCLUDE_DIR NAMES poly/poly.h)
find_library(YICES2_POLY_LIBRARY NAMES poly)
find_path(YICES2_CUDD_INCLUDE_DIR NAMES cudd.h)
find_library(YICES2_CUDD_LIBRARY NAMES cudd)
set(YICES2_MCSAT_ARGS "")
if(
  YICES2_POLY_INCLUDE_DIR
  AND YICES2_POLY_LIBRARY
  AND YICES2_CUDD_INCLUDE_DIR
  AND YICES2_CUDD_LIBRARY
)
  list(APPEND YICES2_MCSAT_ARGS --enable-mcsat)
  get_filename_component(_poly_library_dir "${YICES2_POLY_LIBRARY}" DIRECTORY)
  get_filename_component(_cudd_library_dir "${YICES2_CUDD_LIBRARY}" DIRECTORY)
  list(APPEND _yices2_include_dirs "${YICES2_POLY_INCLUDE_DIR}" "${YICES2_CUDD_INCLUDE_DIR}")
  list(APPEND _yices2_library_dirs "${_poly_library_dir}" "${_cudd_library_dir}")
  message(STATUS "Yices2 is built with MCSAT")
else()
  message(
    STATUS
    "Yices2 is built without MCSAT, which needs LibPoly and CUDD to be "
    "installed, so Yices2 cannot solve nonlinear arithmetic. To add it later, "
    "install both, delete ${SMT_SWITCH_DEPS_DIR}/yices2 and configure again."
  )
endif()

set(YICES2_ENV "")
if(_yices2_include_dirs)
  list(REMOVE_DUPLICATES _yices2_include_dirs)
  list(REMOVE_DUPLICATES _yices2_library_dirs)
  string(REPLACE ";" ":" _yices2_include_dirs "${_yices2_include_dirs}")
  string(REPLACE ";" ":" _yices2_library_dirs "${_yices2_library_dirs}")
  smt_switch_prepend_path(CPATH "${_yices2_include_dirs}" YICES2_CPATH)
  smt_switch_prepend_path(LIBRARY_PATH "${_yices2_library_dirs}" YICES2_LIBRARY_PATH)
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
  COMMAND
    ${YICES2_ENV} <SOURCE_DIR>/configure --enable-thread-safety ${YICES2_MCSAT_ARGS}
    --prefix=<INSTALL_DIR>
  BUILD_COMMAND ${YICES2_ENV} make build_dir=build BUILD=build -j${SMT_SWITCH_DEPS_JOBS}
  # LDCONFIG lives in /usr/sbin, which is not always on a user's PATH, and all
  # it would do is refresh symlinks next to the staged library.
  INSTALL_COMMAND make build_dir=build BUILD=build prefix=<INSTALL_DIR> LDCONFIG=true install
  BUILD_IN_SOURCE TRUE
)
