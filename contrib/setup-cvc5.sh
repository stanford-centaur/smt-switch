#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

CVC5_VERSION=3c37d6aeb7028923ea1827a75de54bd6947b955b

if [ ! -d "$DEPS/cvc5" ]; then
    cd $DEPS
    git clone https://github.com/cvc5/cvc5.git
    chmod -R 777 cvc5
    cd cvc5
    git checkout -f ${CVC5_VERSION}
    CXXFLAGS=-fPIC CFLAGS=-fPIC ./configure.sh --static --auto-download
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
