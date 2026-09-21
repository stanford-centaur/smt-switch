#!/bin/bash
git_commit=8d1eb01093ae54d9b4586456b69c3bf31000a4c2 # 0.9.1
dependencies=(cadical)

configure_step() {
  # Bitwuzla looks for CaDiCaL with the compiler before falling back to
  # pkg-config, and CaDiCaL ships no pkg-config file, so point the compiler
  # at it. Meson reads both variables the way a compiler driver does.
  local cadical_prefix=$deps_dir/cadical
  export CPATH=$cadical_prefix/include${CPATH:+:$CPATH}
  export LIBRARY_PATH=$cadical_prefix/lib${LIBRARY_PATH:+:$LIBRARY_PATH}
  ./configure.py --prefix "$install_dir"
}

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$_setup_script_path")/meson-setup.sh"
