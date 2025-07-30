#!/bin/bash
git_tag=z3-4.14.1
github_owner=Z3Prover
cmake_options=(-DZ3_BUILD_LIBZ3_SHARED=Off)

source "$(dirname "$(realpath "$0")")/cmake-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
