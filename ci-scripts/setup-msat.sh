#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS


usage () {
    cat <<EOF
Usage: $0 [<option> ...]

Downloads the MathSAT SMT Solver. Note this solver is under a custom (non BSD compliant) license.

-h, --help              display this message and exit
-y, --auto-yes          automatically agree to conditions (default: off)
EOF
    exit 0
}

get_msat=default

while [ $# -gt 0 ]
do
    case $1 in
        -h|--help) usage;;
        -y|--auto-yes) get_msat=y;;
        *) die "unexpected argument: $1";;
    esac
    shift
done

if [[ "$get_msat" == default ]]; then
    read -p "MathSAT is distributed under a custom (non-BSD compliant) license. By continuing you acknowledge this distinction and assume responsibility for meeting the license conditions. Continue? [y]es/[n]o: " get_msat
fi

if [[ "$get_msat" != y ]]; then
    echo "Not downloading MathSAT"
    exit 0
fi

RELEASE_URL="https://mathsat.fbk.eu/release/"

if [ ! -d "$DEPS/mathsat" ]; then
    cd $DEPS
    mkdir mathsat
    if [[ "$OSTYPE" == linux* || "$OSTYPE" == cygwin* ]]; then
        curl -o mathsat.tar.gz -L ${RELEASE_URL}mathsat-5.6.12-linux-x86_64.tar.gz
    elif [[ "$OSTYPE" == darwin* ]]; then
        curl -o mathsat.tar.gz -L ${RELEASE_URL}mathsat-5.6.12-macos.tar.gz
    elif [[ "$OSTYPE" == msys* ]]; then
        curl -o mathsat.tar.gz -L ${RELEASE_URL}mathsat-5.6.12-win64.zip
    else
        echo "Unrecognized OSTYPE=$OSTYPE"
        exit 1
    fi

    tar -xf mathsat.tar.gz -C mathsat --strip-components 1
    rm mathsat.tar.gz

else
    echo "$DEPS/mathsat already exists. If you want to re-download, please remove it manually."
fi

if [ -f $DEPS/mathsat/lib/libmathsat.a ] ; then \
    echo "It appears mathsat was setup successfully into $DEPS/mathsat."
    echo "You may now install it with make ./configure.sh --msat && cd build && make"
else
    echo "Downloading mathsat failed."
    echo "Please see their website: http://mathsat.fbk.eu/"
    exit 1
fi
