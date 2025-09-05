#!/bin/bash
git_tag=3.2.4
cmake_options=(-DUSE_CADICAL=ON)

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  "$contrib_dir/setup-btor2tools.sh"
}

source "$(dirname "$(realpath "$0")")/cmake-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
