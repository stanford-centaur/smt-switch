#!/bin/bash
git_commit=befcee5dd12f2183b6a16a5b3d0b0d87fa2edd87
cmake_options=(-DENABLE_AUTO_DOWNLOAD=ON -DUSE_POLY=ON)

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$(realpath "$0")")/cmake-setup.sh"
