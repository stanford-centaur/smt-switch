# CaDiCaL and btor2tools are built by Boolector's own setup scripts, at the
# commits Boolector pins, into <SOURCE_DIR>/deps/install, which Boolector's
# CMake adds to its search path itself.
smt_switch_dependency(
  boolector
  URL "${BOOLECTOR_URL}"
  # Other versions of CaDiCaL are linked by other solvers. To avoid symbols from
  # one libcadical.a leaking into other solvers, the C++ namespace (CaDiCaL::*)
  # is renamed here. Boolector only uses the C API. setup-cadical.sh sets
  # CXXFLAGS itself rather than taking them from outside, so it is patched.
  PATCH_COMMAND
    sed -i.orig "s/CXXFLAGS=\"-fPIC\"/CXXFLAGS=\"-fPIC -DCaDiCaL=smt_switch_btor_CaDiCaL\"/"
    <SOURCE_DIR>/contrib/setup-cadical.sh
  COMMAND <SOURCE_DIR>/contrib/setup-cadical.sh
  # Both Boolector and btor2tools declare CMake versions that are too old, so we
  # need to force a newer minimum policy version. setup-btor2tools.sh also
  # hard-codes make, so other CMake generators like Ninja do not work here.
  COMMAND
    "${CMAKE_COMMAND}" -E env --unset=CMAKE_GENERATOR
    CMAKE_POLICY_VERSION_MINIMUM=${POLICY_VERSION_MINIMUM}
    <SOURCE_DIR>/contrib/setup-btor2tools.sh
  CMAKE_ARGS
    ${COMMON_CMAKE_ARGS}
    ${POLICY_CMAKE_ARGS}
    -DCMAKE_INSTALL_PREFIX=<INSTALL_DIR>
    -DUSE_CADICAL=ON
  BUILD_COMMAND "${CMAKE_COMMAND}" --build <BINARY_DIR> -j${SMT_SWITCH_DEPS_JOBS}
)
