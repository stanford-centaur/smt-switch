#!/bin/bash
git_commit=507893c57fb379743c7a52ad770b0c2525021f4a

download_step() {
  git clone --revision=$git_commit git@github.com:bitwuzla/bitwuzla-interpolants.git $dep_name
}

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

source "$(dirname "$(realpath "$0")")/meson-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
