#!/bin/bash
git_commit=f82d1403b63647e45a5b66d15fc91ca20316348f
cmake_options=(-DENABLE_AUTO_DOWNLOAD=ON -DUSE_POLY=ON)

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

source "$(dirname "$(realpath "$0")")/cmake-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
