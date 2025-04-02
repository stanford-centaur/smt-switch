#!/bin/bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

CVC5_VERSION=f82d1403b63647e45a5b66d15fc91ca20316348f

if [ "$(uname)" == "Darwin" ]; then
    NUM_CORES=$(sysctl -n hw.logicalcpu)
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    NUM_CORES=$(nproc)
else
    NUM_CORES=1
fi

$DIR/setup-cadical.sh

if [ ! -d "$DEPS/cvc5" ]; then
    cd $DEPS
    git clone https://github.com/cvc5/cvc5.git
    chmod -R 777 cvc5
    cd cvc5
    git checkout -f ${CVC5_VERSION}
    CXXFLAGS=-fPIC CFLAGS=-fPIC ./configure.sh --static --auto-download --dep-path="$DEPS/install"
    cd build
    make -j$NUM_CORES
    cd $DIR
else
    echo "$DEPS/cvc5 already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/cvc5/build/src/libcvc5.a ] && [ -f $DEPS/cvc5/build/src/parser/libcvc5parser.a ] && [ -f $DEPS/install/lib/libcadical.a ]; then
    echo "It appears cvc5 was setup successfully into $DEPS/cvc5."
    echo "You may now install it with make ./configure.sh --cvc5 && cd build && make"
else
    echo "Building cvc5 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/cvc5/cvc5"
    exit 1
fi
