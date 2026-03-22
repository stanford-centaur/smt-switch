#!/bin/bash
git_commit=122f27f9518269cd9c1ebf0efced37dfd7f845e6

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

configure_step() {
  ./configure.py --prefix "$install_dir"
}

# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$(realpath "$0")")/meson-setup.sh"
