#!/bin/bash

if [ ! -d "./boolector" ]; then
    git clone https://github.com/Boolector/boolector.git
    cd boolector
    ./contrib/setup-btor2tools.sh
    ./contrib/setup-lingeling.sh
    ./configure.sh --only-lingeling -fPIC
    cd build
    make -j8
    cd ../../
fi

make all
