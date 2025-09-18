#!/bin/bash
git_commit=f896e66eebfe2549fc1d1d11724f3dd50db6e1f1

download_step() {
  git clone --revision=$git_commit git@github.com:bitwuzla/bitwuzla-interpolants.git $dep_name
}

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  patch -p1 <"$contrib_dir/bitwuzla_libgmp.patch"
}

source "$(dirname "$(realpath "$0")")/meson-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
