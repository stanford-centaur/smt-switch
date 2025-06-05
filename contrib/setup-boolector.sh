#!/bin/bash
git_commit=97698b06a5de1a4e5743c034c867d384630dc936
cmake_options=(-DUSE_CADICAL=ON)

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
  "$contrib_dir/setup-btor2tools.sh"
}

source "$(dirname "$(realpath "$0")")/cmake-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
