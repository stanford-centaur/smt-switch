smt_switch_dependency(
  bison
  URL "${BISON_URL}"
  CONFIGURE_COMMAND <SOURCE_DIR>/configure --prefix=<INSTALL_DIR>
  BUILD_COMMAND make -j${SMT_SWITCH_DEPS_JOBS}
  INSTALL_COMMAND make install
  BUILD_IN_SOURCE TRUE
)
