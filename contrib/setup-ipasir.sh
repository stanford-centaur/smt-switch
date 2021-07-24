#!/bin/bash

IPASIR_VERSION=c10e2663b6708223fe5b5f35ff3acf609215f363

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/ipasir" ]; then
    cd $DEPS
    git clone https://github.com/biotomas/ipasir.git
    chmod -R 777 ipasir
    cd ipasir
    git checkout -f $IPASIR_VERSION
    
    ./scripts/mkall.sh
    cd build
    make -j$(nproc)
    cd $DIR
else
    echo "$DEPS/ipasir already exists. If you want to rebuild, please remove it manually."
fi