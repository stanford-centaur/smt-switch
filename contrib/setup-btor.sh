#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/boolector" ]; then
    cd $DEPS
    git clone -b smtcomp19 https://github.com/Boolector/boolector.git
    chmod -R 777 boolector
    cd boolector
    # temporarily pull specific hash
    git checkout 98aeefd27d0ce1188707dda013c1c63a00be7b4c
    ./contrib/setup-btor2tools.sh
    ./contrib/setup-cadical.sh
    ./configure.sh --only-cadical -fPIC
    cd build
    make -j$(nproc)
    cd $DIR
else
    echo "$DEPS/boolector already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/boolector/build/lib/libboolector.a ] && [ -f $DEPS/boolector/deps/lingeling/liblgl.a ] && [ -f $DEPS/boolector/deps/btor2tools/build/btor2parser.o ] ; then \
    echo "It appears boolector was setup successfully into $DEPS/boolector."
    echo "You may now install it with make ./configure.sh --btor && cd build && make"
else
    echo "Building boolector failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/Boolector/boolector"
    exit 1
fi
