#!/bin/bash

# requires autoconf, gperf

YICES2_VERSION=98fa2d882d83d32a07d3b8b2c562819e0e0babd0

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

if [ ! -d "$DEPS/yices2" ]; then
    cd $DEPS
    git clone https://github.com/SRI-CSL/yices2.git
    chmod -R 777 yices2
    cd yices2
    git checkout -f $YICES2_VERSION
    autoconf
    ./configure
    make build_dir=build BUILD=build -j$NUM_CORES
    cd $DIR
else
    echo "$DEPS/yices2 already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/yices2/build/lib/libyices.a ] ; then \
    echo "It appears yices2 was setup successfully into $DEPS/yices2."
    echo "You may now install it with make ./configure.sh --yices2 && cd build && make"
else
    echo "Building yices2 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/SRI-CSL/yices2"
    exit 1
fi



