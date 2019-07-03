#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
CVC4_HOME=$DIR/../cvc4

if [ ! -d "$CVC4_HOME/CVC4" ]; then
    cd $CVC4_HOME
    git clone https://github.com/CVC4/CVC4.git
    chmod -R 777 CVC4
    cd CVC4
    ./contrib/get-antlr-3.4
    CXXFLAGS=-fPIC CFLAGS=-fPIC ./configure.sh --static
    cd build
    make -j$(nproc)
    cd $DIR
fi

if [ -f $CVC4_HOME/CVC4/build/src/libcvc4.a ] && [ -f $CVC4_HOME/CVC4/build/src/parser/libcvc4parser.a ]; then
    echo "It appears CVC4 was setup successfully into $CVC4_HOME/CVC4."
    echo "You may now install it with make install-cvc4"
else
    echo "Building CVC4 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/CVC4/CVC4"
fi
