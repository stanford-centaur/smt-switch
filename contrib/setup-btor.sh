#!/bin/bash

BTOR_VERSION=97698b06a5de1a4e5743c034c867d384630dc936
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


if [ ! -d "$DEPS/boolector" ]; then
    cd $DEPS
    git clone https://github.com/Boolector/boolector.git
    chmod -R 777 boolector
    cd boolector
    git checkout -f $BTOR_VERSION
    CFLAGS="" ./contrib/setup-btor2tools.sh
    ./contrib/setup-cadical.sh
    ./configure.sh --only-cadical -fPIC
    cd build
    make -j$NUM_CORES
    cd $DIR
else
    echo "$DEPS/boolector already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/boolector/build/lib/libboolector.a ] && [ -f $DEPS/boolector/deps/cadical/build/libcadical.a ] && [ -f $DEPS/boolector/deps/btor2tools/build/btor2parser.o ] ; then \
    echo "It appears boolector was setup successfully into $DEPS/boolector."
    echo "You may now install it with make ./configure.sh --btor && cd build && make"
else
    echo "Building boolector failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/Boolector/boolector"
    exit 1
fi
