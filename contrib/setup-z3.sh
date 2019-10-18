#!/bin/bash

Z3_VERSION=724a42b6f28f1c25b2b05a21e5947f11015612be

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/z3" ]; then
    cd $DEPS
    git clone https://github.com/Z3Prover/z3.git
    chmod -R 777 z3
    cd z3
    git checkout -f $Z3_VERSION
    ./configure --staticlib
    python scripts/mk_make.py
    cd build
    make -j$(nproc)
    cd $DIR
else
    echo "$DEPS/z3 already exists. If you want to rebuild, please remove it manually."
fi
#
#if [ -f $DEPS/boolector/build/lib/libboolector.a ] && [ -f $DEPS/boolector/deps/lingeling/liblgl.a ] && [ -f $DEPS/boolector/deps/btor2tools/build/btor2parser.o ] ; then \
#    echo "It appears boolector was setup successfully into $DEPS/boolector."
#    echo "You may now install it with make ./configure.sh --btor && cd build && make"
#else
#    echo "Building boolector failed."
#    echo "You might be missing some dependencies."
#    echo "Please see their github page for installation instructions: https://github.com/Boolector/boolector"
#    exit 1
#fi
