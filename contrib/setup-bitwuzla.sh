#!/bin/bash
git_commit=e91f81ee21e32ef91f1a4c6f9341281179f952d5

download_step() {
  git clone --revision=$git_commit git@github.com:bitwuzla/bitwuzla-interpolants.git $dep_name
}

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  patch -p1 <"$contrib_dir/bitwuzla_libgmp.patch"
}

source "$(dirname "$(realpath "$0")")/meson-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
