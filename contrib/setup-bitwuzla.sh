#!/bin/bash
git_commit=122f27f9518269cd9c1ebf0efced37dfd7f845e6

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

configure_step() {
  ./configure.py --prefix "$install_dir"
}

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$_setup_script_path")/meson-setup.sh"
