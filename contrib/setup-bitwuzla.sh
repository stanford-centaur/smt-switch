#!/bin/bash
git_commit=0ef2ebff4f52239a3b7d5309c25b4e535b60a12d

download_step() {
  git clone --revision=$git_commit git@github.com:bitwuzla/bitwuzla-interpolants.git $dep_name
}

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  patch -p1 <"$contrib_dir/bitwuzla_libgmp.patch"
}

# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$(realpath "$0")")/meson-setup.sh"
