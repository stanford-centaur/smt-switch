#!/usr/bin/env bash
#
# This script is meant to build the smt-switch C++ libraries for the PyPi upload
# cibuildwheel (abbreviated cibw) will take care of building and packaging the Python wheel

./contrib/setup-bitwuzla.sh
./contrib/setup-cvc5.sh
./contrib/setup-z3.sh

# Find the Python root directory for the current Python version
# This is important for the manylinux infrastructure, which is in
# a nonstandard location that CMake has trouble finding
PYTHON_EXECUABLE=$(which python3)
PYTHON_ROOT=$(dirname $(dirname $(realpath ${PYTHON_EXECUTABLE})))

./configure.sh --bitwuzla --cvc5 --z3 --python --python-executable=${PYTHON_EXECUTABLE} --python-root-dir=${PYTHON_ROOT}
cd build
make -j
