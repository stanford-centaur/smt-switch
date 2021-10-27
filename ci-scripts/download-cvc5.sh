#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS


usage () {
    cat <<EOF
Usage: $0 [<option> ...]

Downloads a precompiled cvc5 SMT Solver,

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

if [ ! -d "$DEPS/cvc5" ]; then
    cd $DEPS
    if [[ "$OSTYPE" == linux* ]]; then
        curl -o cvc5.tar.xz -L http://web.stanford.edu/~makaim/files/cvc5-linux.tar.xz
    elif [[ "$OSTYPE" == darwin* ]]; then
        curl -o cvc5.tar.xz -L http://web.stanford.edu/~makaim/files/cvc5-mac.tar.xz
    elif [[ "$OSTYPE" == msys* ]]; then
        echo "Pre-compiled libraries for Windows not yet available"
    elif [[ "$OSTYPE" == cygwin* ]]; then
        curl -o cvc5.tar.xz -L http://web.stanford.edu/~makaim/files/cvc5-linux.tar.xz
    else
        echo "Unrecognized OSTYPE=$OSTYPE"
        exit 1
    fi

    tar -xf cvc5.tar.xz
    rm cvc5.tar.xz

else
    echo "$DEPS/cvc5 already exists. If you want to re-download, please remove it manually."
    exit 1
fi

if [ -f $DEPS/cvc5/build/src/libcvc5.a ] ; then \
    echo "It appears cvc5 was setup successfully into $DEPS/cvc5."
    echo "You may now install it with make ./configure.sh --cvc5 && cd build && make"
else
    echo "Downloading cvc5 failed."
    exit 1
fi
