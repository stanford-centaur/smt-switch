#!/bin/bash
git_commit=f82d1403b63647e45a5b66d15fc91ca20316348f

source "$(dirname "$(realpath "$0")")/common-setup.sh"

"$contrib_dir/setup-cadical.sh"

# Ensure that the cvc5 libraries are placed in deps/install/lib.
./configure.sh --static --auto-download --dep-path="$install_dir" --prefix="$install_dir" -DCMAKE_INSTALL_LIBDIR=lib
cmake --build build -j$num_cores
cmake --install build
