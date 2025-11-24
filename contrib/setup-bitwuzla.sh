#!/bin/bash
git_commit=42fc6749a2df0f9ef5b9482927b2e745af810ba9

download_step() {
  git clone --revision=$git_commit git@github.com:bitwuzla/bitwuzla-interpolants.git "$dep_name"
}

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  # Remove GMP subproject -- broken, has been removed on main
  sed -i 14,28d src/meson.build
  rm -f subprojects/gmp-6.3.0.wrap
  rm -rf subprojects/packagefiles/gmp-6.3.0
}

# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$(realpath "$0")")/meson-setup.sh"
