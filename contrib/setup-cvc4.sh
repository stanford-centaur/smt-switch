#!/bin/bash

CVC4_VERSION=75cd4fe254f1f4de846b5cf9489b591dffbca333

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/CVC4" ]; then
    cd $DEPS
    git clone https://github.com/CVC4/CVC4.git
    chmod -R 777 CVC4
    cd CVC4
    git checkout -f $CVC4_VERSION
    echo "try wget directly"
    wget -c -O ./antlr-3.4-complete_wget.jar "https://www.antlr3.org/download/antlr-3.4-complete.jar"
    echo "try curl directly"
    curl -L "https://www.antlr3.org/download/antlr-3.4-complete.jar" > ./antlr-3.4-complete_curl.jar
    echo "try copied script"
    $DEPS/../contrib/get-antlr-test
    echo "before CVC4 get-antlr-3.4"
    ./contrib/get-antlr-3.4
    # git clone https://github.com/uiri/toml.git
    # export PYTHONPATH=$PYTHONPATH:`pwd`/toml
    # CXXFLAGS=-fPIC CFLAGS=-fPIC ./configure.sh --static --no-static-binary
    # cd build
    # make -j4
    # cd $DIR
else
    echo "$DEPS/CVC4 already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/CVC4/build/src/libcvc4.a ] && [ -f $DEPS/CVC4/build/src/parser/libcvc4parser.a ]; then
    echo "It appears CVC4 was setup successfully into $DEPS/CVC4."
    echo "You may now install it with make ./configure.sh --cvc4 && cd build && make"
else
    echo "Building CVC4 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/CVC4/CVC4"
    exit 1
fi
