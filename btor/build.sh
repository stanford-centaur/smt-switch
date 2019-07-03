#!/bin/bash

if [ ! -d "./boolector" ]; then
    git clone https://github.com/Boolector/boolector.git
    chmod -R 777 boolector
    cd boolector
    ./contrib/setup-btor2tools.sh
    ./contrib/setup-lingeling.sh
    ./configure.sh --only-lingeling -fPIC
    cd build
    make -j$(nproc)
    cd ../../
fi
