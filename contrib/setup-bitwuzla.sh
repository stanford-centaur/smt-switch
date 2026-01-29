#!/bin/bash
git_commit=f69eaa2f7f6f81918b45fc9f790bf70203fe0ac8

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

# shellcheck source=contrib/meson-setup.sh
source "$(dirname "$(realpath "$0")")/meson-setup.sh"
