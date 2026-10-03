# ENABLE_AUTO_DOWNLOAD lets cvc5 fetch the dependencies we do not provision,
# CaDiCaL among them, so that the version it gets is the one it pins; USE_POLY
# brings in libpoly for nonlinear arithmetic.
smt_switch_dependency(
  cvc5
  URL "${CVC5_URL}"
  # Ask for a library name nothing provides, so that the lookup fails and cvc5
  # downloads its CaDiCaL instead of linking one from the machine, which it
  # would then not install.
  PATCH_COMMAND
    sed -i.orig "s/find_library(CaDiCaL_LIBRARIES NAMES cadical)/find_library(CaDiCaL_LIBRARIES NAMES cadical-not-installed)/"
    <SOURCE_DIR>/cmake/FindCaDiCaL.cmake
  CMAKE_ARGS
    ${COMMON_CMAKE_ARGS}
    -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
    -DENABLE_AUTO_DOWNLOAD=ON
    -DUSE_POLY=ON
  BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> -j${SMT_SWITCH_DEPS_JOBS}
  INSTALL_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> --target install
  # Drop the C API from the CaDiCaL a static cvc5 installs beside itself. It
  # is not namespaced, Boolector's copy defines the same names, and cvc5 does
  # not use any of it.
  COMMAND ar d <INSTALL_DIR>/${CMAKE_INSTALL_LIBDIR}/libcadical.a ccadical.o ipasir.o
)
