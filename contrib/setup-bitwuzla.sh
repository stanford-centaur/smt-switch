#!/bin/bash
set -e

BITWUZLA_VERSION=229c0fa35bfbdcae7189558f98911a24909a7f04
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS="$( cd "$( dirname "$DIR" )/deps" && pwd )"

mkdir -p $DEPS

if [ "$(uname)" == "Darwin" ]; then
    NUM_CORES=$(sysctl -n hw.logicalcpu)
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    NUM_CORES=$(nproc)
else
    NUM_CORES=1
fi


if [ ! -d "$DEPS/bitwuzla" ]; then
    cd $DEPS
    git clone https://github.com/bitwuzla/bitwuzla.git
    cd bitwuzla
    git checkout -f $BITWUZLA_VERSION
    ./configure.py --prefix $DEPS/install
    cd build
    meson compile
    meson install
else
    echo "$DEPS/bitwuzla already exists. If you want to rebuild, please remove it manually."
fi
