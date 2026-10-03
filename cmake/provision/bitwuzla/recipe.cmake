# Bitwuzla builds its own version of CaDiCaL, which would collide with the
# copies used by boolector and cvc5, so we rename its namespace while compiling.
# Reap is an internal data structure that CaDiCaL oddly puts in the global
# namespace, so we also need to rename it.
set(BITWUZLA_CADICAL "-DCaDiCaL=smt_switch_bzla_CaDiCaL -DReap=smt_switch_bzla_Reap")

# The plain COMMAND options are run after the step they follow.
smt_switch_dependency(
  bitwuzla
  URL "${BITWUZLA_URL}"
  # Ask for a library name nothing provides, so that the lookup fails and
  # Bitwuzla falls through to its wrap instead of linking a CaDiCaL from the
  # machine, which would carry none of the patches the wrap applies.
  PATCH_COMMAND
    sed -i.orig "s/find_library('cadical',/find_library('cadical-not-installed',/"
    <SOURCE_DIR>/src/meson.build
  # Drop the C API from the CaDiCaL build. It is not namespaced, so the renaming
  # fix does not apply, but bitwuzla does not use any of it.
  COMMAND
    sed -i.orig -e "/'ccadical.cpp',/d" -e "/'ipasir.cpp',/d"
    <SOURCE_DIR>/subprojects/packagefiles/cadical/src/meson.build
  CONFIGURE_COMMAND
    <SOURCE_DIR>/configure.py --prefix <INSTALL_DIR>
  COMMAND
    meson configure <SOURCE_DIR>/build "-Dcpp_args=${BITWUZLA_CADICAL}"
    "-Dcadical:cpp_args=${BITWUZLA_CADICAL}"
  BUILD_COMMAND meson compile -C <SOURCE_DIR>/build
  INSTALL_COMMAND meson install -C <SOURCE_DIR>/build
  BUILD_IN_SOURCE TRUE
)
