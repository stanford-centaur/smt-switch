#!/bin/bash
version=2.6.4
url=https://github.com/westes/flex/releases/download/v$version/flex-$version.tar.gz

source "$(dirname "$0")/common-setup.sh"

./configure --prefix "$install_dir"
make -j$num_cores
make install
