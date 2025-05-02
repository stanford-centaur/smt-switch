#!/bin/bash
set -e

Z3_VERSION=z3-4.14.1

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
ROOT_DIR="$(dirname "$SCRIPT_DIR")"
DEPS_DIR="$ROOT_DIR/deps"
INSTALL_DIR="$DEPS_DIR/install"

if [ "$(uname)" == "Darwin" ]; then
    NUM_CORES=$(sysctl -n hw.logicalcpu)
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    NUM_CORES=$(nproc)
else
    NUM_CORES=1
fi

mkdir -p "$DEPS_DIR" && cd "$DEPS_DIR"

if [ ! -d z3 ]; then
    git clone https://github.com/Z3Prover/z3.git && cd z3
    git checkout -f $Z3_VERSION
    mkdir build && cd build
    # a static binary linked to z3 often segfaults due to
    # a pthread related issue
    # compiling with --single-threaded helps, but isn't a real solution
    # see https://github.com/Z3Prover/z3/issues/4554
    cmake .. -DZ3_BUILD_LIBZ3_SHARED=Off -DCMAKE_INSTALL_PREFIX="$INSTALL_DIR"
    cmake --build . -j$NUM_CORES
    cmake --install .
else
    echo "$DEPS_DIR/z3 already exists. If you want to rebuild z3, please remove it manually."
fi

if [ -f "$INSTALL_DIR/lib/libz3.a" ]; then
    echo "It appears z3 is successfully installed into $INSTALL_DIR."
    echo "You may now use it with smt-switch by invoking ./configure.sh --z3 && cd build && make"
else
    echo "Building z3 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/Z3Prover/z3"
    exit 1
fi
