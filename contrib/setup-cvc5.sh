#!/bin/bash
set -e

CVC5_VERSION=d9d5ad1b42d32fc2253d5abaf850b9ca8a20053f

CONTRIB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
SOURCE_DIR="$(dirname "$CONTRIB_DIR")"
DEPS_DIR="$SOURCE_DIR/deps"
INSTALL_DIR="$DEPS_DIR/install"
LIB_DIR="$INSTALL_DIR/lib"

if [ "$(uname)" == "Darwin" ]; then
    NUM_CORES=$(sysctl -n hw.logicalcpu)
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    NUM_CORES=$(nproc)
else
    NUM_CORES=1
fi

mkdir -p "$DEPS_DIR" && cd "$DEPS_DIR"

if [ ! -d cvc5 ]; then
    "$CONTRIB_DIR/setup-cadical.sh"
    git clone https://github.com/cvc5/cvc5.git && cd cvc5
    git checkout -f $CVC5_VERSION
    # ensure the cvc5 libraries are placed in deps/install/lib
    ./configure.sh --static --auto-download --dep-path="$INSTALL_DIR" --prefix="$INSTALL_DIR" -DCMAKE_INSTALL_LIBDIR=lib
    cmake --build build --target install -j$NUM_CORES
else
    echo "$DEPS_DIR/cvc5 already exists. If you want to rebuild, please remove it manually."
fi

if [ -f $LIB_DIR/libcvc5.a ] && [ -f $LIB_DIR/libcvc5parser.a ] && [ -f $LIB_DIR/libcadical.a ]; then
    echo "It appears cvc5 was setup successfully into $INSTALL_DIR."
    echo "You may now configure smt-switch to build with a cvc5 backend using ./configure.sh --cvc5 && cd build && make"
else
    echo "Building cvc5 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/cvc5/cvc5"
    exit 1
fi
