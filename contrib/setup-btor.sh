#!/bin/bash

BTOR_VERSION=5a3b5c88ea9c9dcf4232e33546f69d80d7424b13

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/boolector" ]; then
    cd $DEPS
    git clone -b smtcomp19 https://github.com/Boolector/boolector.git
    chmod -R 777 boolector
    cd boolector
    git checkout -f $BTOR_VERSION
    ./contrib/setup-btor2tools.sh
    ./contrib/setup-cadical.sh
    ./configure.sh --only-cadical -fPIC
    cd build
    make -j$(nproc)
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
