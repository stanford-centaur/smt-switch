#!/bin/bash
git_tag=z3-4.14.1
github_owner=Z3Prover
cmake_options=(-DZ3_BUILD_LIBZ3_SHARED=Off)

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$_setup_script_path")/cmake-setup.sh"
