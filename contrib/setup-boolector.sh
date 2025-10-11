#!/bin/bash
git_tag=3.2.4
cmake_options=(-DUSE_CADICAL=ON)

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  "$contrib_dir/setup-btor2tools.sh"
}

# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$(realpath "$0")")/cmake-setup.sh"
