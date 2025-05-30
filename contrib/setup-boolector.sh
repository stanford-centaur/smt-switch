#!/bin/bash
git_commit=97698b06a5de1a4e5743c034c867d384630dc936

source "$(dirname "$(realpath "$0")")/common-setup.sh"

"$contrib_dir/setup-cadical.sh"

# CMake 4.0 and later require the minimum version to be at least 3.5
export CMAKE_POLICY_VERSION_MINIMUM=3.5
# Ensure that the boolector libraries are placed in deps/install/lib.
export CMAKE_OPTS="-DCMAKE_INSTALL_LIBDIR=lib"
./contrib/setup-btor2tools.sh
./configure.sh --only-cadical -fPIC --path "$install_dir" --prefix "$install_dir"
cmake --build build -j$num_cores
cmake --install build
