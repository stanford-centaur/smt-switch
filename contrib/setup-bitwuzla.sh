#!/bin/bash
set -e

BITWUZLA_VERSION=229c0fa35bfbdcae7189558f98911a24909a7f04
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

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
    ./configure.py
    meson compile -C build
else
    echo "$DEPS/bitwuzla already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/bitwuzla/build/lib/libbitwuzla.a ] && [ -f $DEPS/bitwuzla/deps/cadical/build/libcadical.a ] && [ -f $DEPS/bitwuzla/deps/btor2tools/build/lib/libbtor2parser.a ] ; then \
    echo "It appears bitwuzla was setup successfully into $DEPS/bitwuzla."
    echo "You may now install it with make ./configure.sh --bitwuzla && cd build && make"
else
    echo "Building bitwuzla failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/Bitwuzla/bitwuzla"
    exit 1
fi
