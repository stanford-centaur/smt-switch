#!/bin/bash

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/mathsat" ]; then
    cd $DEPS
    mkdir mathsat
    if [[ "$OSTYPE" == linux* ]]; then
        wget -O mathsat.tar.gz mathsat.fbk.eu/download.php?file=mathsat-5.5.4-linux-x86_64.tar.gz
    elif [[ "$OSTYPE" == darwin* ]]; then
        wget -O mathsat.tar.gz mathsat.fbk.eu/download.php?file=mathsat-5.5.4-darwin-libcxx-x86_64.tar.gz
    elif [[ "$OSTYPE" == msys* ]]; then
        wget -O mathsat.tar.gz mathsat.fbk.eu/download.php?file=mathsat-5.5.4-win64-msvc.zip
    elif [[ "$OSTYPE" == cygwin* ]]; then
        wget -O mathsat.tar.gz mathsat.fbk.eu/download.php?file=mathsat-5.5.4-linux-x86_64.tar.gz
    else
        echo "Unrecognized OSTYPE=$OSTYPE"
        exit 1
    fi

    tar -xf mathsat.tar.gz -C mathsat --strip-components 1
    rm mathsat.tar.gz

else
    echo "$DEPS/mathsat already exists. If you want to rebuild, please remove it manually."
    exit 1
fi

if [ -f $DEPS/mathsat/lib/libmathsat.a ] ; then \
    echo "It appears mathsat was setup successfully into $DEPS/mathsat."
    echo "You may now install it with make ./configure.sh --msat && cd build && make"
else
    echo "Downloading mathsat failed."
    echo "Please see their website: http://mathsat.fbk.eu/"
    exit 1
fi
