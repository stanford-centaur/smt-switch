#!/bin/bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

CVC5_VERSION=f82d1403b63647e45a5b66d15fc91ca20316348f

if [ "$(uname)" == "Darwin" ]; then
    NUM_CORES=$(sysctl -n hw.logicalcpu)
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    NUM_CORES=$(nproc)
else
    NUM_CORES=1
fi

$DIR/setup-cadical.sh

if [ ! -d "$DEPS/cvc5" ]; then
    cd $DEPS
    git clone https://github.com/cvc5/cvc5.git
    cd cvc5
    git checkout -f ${CVC5_VERSION}
    ./configure.sh --prefix=$DEPS/install --static --auto-download --dep-path="$DEPS/install" -DCMAKE_INSTALL_LIBDIR=lib
    cd build
    make -j$NUM_CORES
    make install
    cd $DIR
else
    echo "$DEPS/cvc5 already exists. If you want to rebuild, please remove it manually."
fi

LIBS="$DEPS/install/lib"

if [ -f $LIBS/libcvc5.a ] && [ -f $LIBS/libcvc5parser.a ] && [ -f $LIBS/libcadical.a ]; then
    echo "It appears cvc5 was setup successfully into $DEPS/install."
    echo "You may now configure smt-switch to build with a cvc5 backend using ./configure.sh --cvc5 && cd build && make"
else
    echo "Building cvc5 failed."
    echo "You might be missing some dependencies."
    echo "Please see their github page for installation instructions: https://github.com/cvc5/cvc5"
    exit 1
fi
