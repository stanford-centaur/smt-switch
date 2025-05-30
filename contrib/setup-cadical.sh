#!/bin/bash
git_tag=rel-2.1.3
github_owner=arminbiere

source "$(dirname "$0")/common-setup.sh"

./configure CXXFLAGS="-fPIC"
make -j$num_cores
install -m644 build/libcadical.a "$install_libdir"
install -m644 src/ccadical.h "$install_includedir"
install -m644 src/cadical.hpp "$install_includedir"
