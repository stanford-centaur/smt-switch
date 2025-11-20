#!/bin/bash
git_commit=42fc6749a2df0f9ef5b9482927b2e745af810ba9

download_step() {
  git clone --revision=$git_commit git@github.com:bitwuzla/bitwuzla-interpolants.git $dep_name
}

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  patch -p1 <"$contrib_dir/bitwuzla_cadical220.patch"
  patch -p1 <"$contrib_dir/bitwuzla_libgmp.patch"
}

# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$(realpath "$0")")/meson-setup.sh"
