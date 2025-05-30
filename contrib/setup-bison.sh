#!/bin/bash
version=3.8.2
url=https://ftp.gnu.org/gnu/bison/bison-$version.tar.gz

source "$(dirname "$0")/common-setup.sh"

./configure --prefix "$install_dir"
make -j$num_cores
make install
