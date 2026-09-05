#!/bin/bash
git_tag=3.2.4
cmake_options=(-DUSE_CADICAL=ON)

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  "$contrib_dir/setup-btor2tools.sh"
}

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$_setup_script_path")/cmake-setup.sh"
