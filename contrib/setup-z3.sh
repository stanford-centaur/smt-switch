#!/bin/bash
set -e

Z3_VERSION=z3-4.12.6

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

if [ ! -d "$DEPS/z3" ]; then
    cd $DEPS
    git clone https://github.com/Z3Prover/z3.git
    chmod -R 777 z3
    cd z3
    git checkout -f $Z3_VERSION
    # a static binary linked to z3 often segfaults due to
    # a pthread related issue
    # compiling with --single-threaded helps, but isn't a real solution
    # see https://github.com/Z3Prover/z3/issues/4554
    # ./configure --staticlib --single-threaded
    cmake -S . -B build -DCMAKE_BUILD_TYPE=Release -DZ3_BUILD_LIBZ3_SHARED=Off -DZ3_BUILD_LIBZ3_MSVC_STATIC=On
    cmake --build build -j$NUM_CORES
    cd $DIR
else
    echo "$DEPS/z3 already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $DEPS/z3/build/libz3.a ]; then
    echo "It appears z3 was setup successfully into $DEPS/z3."
    echo "You may now install it with make ./configure.sh --z3 && cd build && make"
else
    echo "Building z3 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/z3/z3"
    exit 1
fi
