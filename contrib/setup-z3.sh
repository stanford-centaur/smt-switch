#!/bin/bash
git_tag=z3-4.14.1
github_owner=Z3Prover

source "$(dirname "$(realpath "$0")")/common-setup.sh"

# Ensure that the z3 libraries are placed in deps/install/lib.
cmake -S . -B build -DZ3_BUILD_LIBZ3_SHARED=Off -DCMAKE_INSTALL_PREFIX="$install_dir" -DCMAKE_INSTALL_LIBDIR=lib
cmake --build build -j$num_cores
cmake --install build
