#!/usr/bin/env bash
#
# This script is meant to build the smt-switch C++ libraries for the PyPi upload
# cibuildwheel (abbreviated cibw) will take care of building and packaging the Python wheel

# Find the Python root directory for the current Python version
# This is important for the manylinux infrastructure, which is in
# a nonstandard location that CMake has trouble finding
PYTHON_EXECUTABLE=$(realpath $(which python3))
PYTHON_ROOT=$(dirname $(dirname ${PYTHON_EXECUTABLE}))

echo "Identified Python executable and root directory as:"
echo "Python_EXECUTABLE: ${PYTHON_EXECUTABLE}"
echo "Python_ROOT_DIR: ${PYTHON_ROOT}"

# TODO: determine if we need this or not
# if [ "$(uname)" = "Darwin" ]; then
#     echo "Running on macOS - using Python executable only" &&
#     CMAKE_PYTHON_OPTIONS="--python-executable=${PYTHON_EXECUTABLE}"
# else
#     echo "Running on Linux - using python root dir" &&
#     CMAKE_PYTHON_OPTIONS="--python-root-dir=$PYTHON_ROOT"
# fi

./contrib/setup-bitwuzla.sh
./contrib/setup-cvc5.sh
./contrib/setup-z3.sh

./configure.sh --bitwuzla --cvc5 --z3 --python --python-root-dir=${PYTHON_ROOT}
cd build
make -j
