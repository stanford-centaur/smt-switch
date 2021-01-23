#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS


usage () {
    cat <<EOF
Usage: $0 [<option> ...]

Downloads a precompiled CVC4 SMT Solver,

-h, --help              display this message and exit
EOF
    exit 0
}

while [ $# -gt 0 ]
do
    case $1 in
        -h|--help) usage;;
        *) die "unexpected argument: $1";;
    esac
    shift
done

if [ ! -d "$DEPS/CVC4" ]; then
    cd $DEPS
    if [[ "$OSTYPE" == linux* ]]; then
        curl -o CVC4.tar.bz2 -L http://web.stanford.edu/~makaim/files/CVC4-linux-new.tar.bz2
    elif [[ "$OSTYPE" == darwin* ]]; then
        curl -o CVC4.tar.bz2 -L http://web.stanford.edu/~makaim/files/CVC4-mac-new.tar.bz2
    elif [[ "$OSTYPE" == msys* ]]; then
        echo "Pre-compiled libraries for Windows not yet available"
    elif [[ "$OSTYPE" == cygwin* ]]; then
        curl -o CVC4.tar.bz2 -L http://web.stanford.edu/~makaim/files/CVC4-linux-new.tar.bz2
    else
        echo "Unrecognized OSTYPE=$OSTYPE"
        exit 1
    fi

    tar -xf CVC4.tar.bz2
    rm CVC4.tar.bz2

else
    echo "$DEPS/CVC4 already exists. If you want to re-download, please remove it manually."
    exit 1
fi

if [ -f $DEPS/CVC4/build/src/libcvc4.a ] ; then \
    echo "It appears CVC4 was setup successfully into $DEPS/CVC4."
    echo "You may now install it with make ./configure.sh --msat && cd build && make"
else
    echo "Downloading CVC4 failed."
    exit 1
fi
