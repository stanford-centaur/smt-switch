#!/bin/bash

if [ ! -d "./CVC4" ]; then
    git clone https://github.com/CVC4/CVC4.git
    cd CVC4
    ./contrib/get-antlr-3.4
    ./configure.sh
    cd build
    make -j16
    cd ../../
fi

make all
