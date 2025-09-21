#!/bin/bash
git_commit=8a6ee199d9a955051c454a6a741fb514d30d1fbd

download_step() {
  git clone --revision=$git_commit git@github.com:bitwuzla/bitwuzla-interpolants.git $dep_name
}

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  patch -p1 <"$contrib_dir/bitwuzla_libgmp.patch"
}

source "$(dirname "$(realpath "$0")")/meson-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
