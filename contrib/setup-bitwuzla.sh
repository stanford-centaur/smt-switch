#!/bin/bash
git_commit=2e7204ac7344947d5f8ee1eb8b3812ec9981cedf

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$(realpath "$0")")/meson-setup.sh"
