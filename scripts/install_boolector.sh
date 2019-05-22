#!/bin/bash

git clone https://github.com/Boolector/boolector.git
cd boolector
./contrib/setup-btor2tools.sh
./contrib/setup-lingeling.sh
./configure.sh --only-lingeling
cd build
make -j16
