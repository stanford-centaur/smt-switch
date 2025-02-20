#!/usr/bin/env bash
#
# This script is meant to build the smt-switch C++ libraries for the PyPi upload
# cibuildwheel (abbreviated cibw) will take care of building and packaging the Python wheel

set -e

# Find the Python root directory for the current Python version
# This is important for the manylinux infrastructure, which is in
# a nonstandard location that CMake has trouble finding
PYTHON_EXECUTABLE=$(realpath $(which python3))
echo "Using Python_EXECUTABLE: ${PYTHON_EXECUTABLE}"

./contrib/setup-bitwuzla.sh
# the version of ld.gold is too old in manylinux_2_28, remove it so cvc5 falls back on bfd
rm -f /usr/bin/ld.gold
./contrib/setup-cvc5.sh
./contrib/setup-z3.sh

./configure.sh --bitwuzla --cvc5 --z3 --python --python-executable=${PYTHON_EXECUTABLE}
cd build
make -j
