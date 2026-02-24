#!/bin/bash
git_commit=86cecd83b685f59e884094693b9a4c5c90a62e03
cmake_options=(-DENABLE_AUTO_DOWNLOAD=ON -DUSE_POLY=ON)

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$(realpath "$0")")/cmake-setup.sh"
