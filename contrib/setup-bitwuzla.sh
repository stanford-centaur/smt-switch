#!/bin/bash
git_commit=8d1eb01093ae54d9b4586456b69c3bf31000a4c2 # 0.9.1
dependencies=(cadical)

configure_step() {
  ./configure.py --prefix "$install_dir"
}

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$_setup_script_path")/meson-setup.sh"
