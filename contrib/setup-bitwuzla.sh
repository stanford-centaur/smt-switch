#!/bin/bash

BITWUZLA_VERSION=6e46391816b4baf8c9fc0b8c0c1d2fbe63b6f30e
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
    chmod -R 777 bitwuzla
    cd bitwuzla
    git checkout -f $BITWUZLA_VERSION
    CFLAGS="" ./contrib/setup-btor2tools.sh
    ./contrib/setup-cadical.sh
    ./configure.sh --only-cadical --no-symfpu -fPIC
    cd build
    make -j$NUM_CORES
    cd $DIR
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
