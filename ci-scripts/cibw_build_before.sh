#!/usr/bin/env bash
#
# This script is meant to build the smt-switch C++ libraries for the PyPi upload
# cibuildwheel (abbreviated cibw) will take care of building and packaging the Python wheel

./contrib/setup-bitwuzla.sh
./contrib/setup-cvc5.sh
./contrib/setup-z3.sh

source ./.venv/bin/activate
./configure.sh --bitwuzla --cvc5 --z3 --python --python-executable=$(which python3)
cd build
make -j
# cibuildwheel doesn't want the generated .so file for the packaged Python
# That happens automatically when built with python bindings
# delete them now and let cibuildwheel do the packaging
find ./build/python -name "*.so" -delete
find ./build/python -name "*.o" -delete
