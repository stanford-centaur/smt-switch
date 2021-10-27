#!/bin/bash

CVC5_VERSION=f493ea93e925e3ad9bfe0036e1d876d5600d5b30

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/cvc5" ]; then
    cd $DEPS
    git clone https://github.com/cvc5/cvc5.git
    git checkout -f ${CVC5_VERSION}
    chmod -R 777 cvc5
    cd cvc5
    CXXFLAGS=-fPIC CFLAGS=-fPIC ./configure.sh --static --no-static-binary --auto-download
    cd build
    make -j4
    cd $DIR
else
    echo "$DEPS/cvc5 already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/cvc5/build/src/libcvc5.a ] && [ -f $DEPS/cvc5/build/src/parser/libcvc5parser.a ]; then
    echo "It appears cvc5 was setup successfully into $DEPS/cvc5."
    echo "You may now install it with make ./configure.sh --cvc5 && cd build && make"
else
    echo "Building cvc5 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/cvc5/cvc5"
    exit 1
fi
