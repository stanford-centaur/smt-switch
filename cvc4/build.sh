#!/bin/bash

if [ ! -d "./CVC4" ]; then
    git clone https://github.com/CVC4/CVC4.git
    chmod -R 777 CVC4
    cd CVC4
    ./contrib/get-antlr-3.4
    CXXFLAGS=-fPIC CFLAGS=-fPIC ./configure.sh --static
    cd build
    make -j$(nproc)
    cd ../../
fi
