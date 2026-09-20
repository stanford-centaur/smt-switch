#!/bin/bash
git_commit=0b6cdcdbc65da25ef0f73ac9da210574d0f66cf8 # z3-5.1.0
github_owner=Z3Prover
cmake_options=(-DZ3_BUILD_LIBZ3_SHARED=Off)

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$_setup_script_path")/cmake-setup.sh"
