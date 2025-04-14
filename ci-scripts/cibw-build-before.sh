#!/usr/bin/env bash
###############################################################################
# Top contributors (to current version):
#  Makai Mann 
#
#  This file is part of the smt-switch project.
#
#  Copyright (c) 2025 by the authors listed in the file AUTHORS
#  in the top-level source directory) and their institutional affiliations.
#  All rights reserved.  See the file LICENSE in the top-level source
#  directory for licensing information.\endverbatim
###############################################################################
#
# This script builds the smt-switch C++ libraries for the PyPi upload
# It is meant to be run after cibw-build-deps.sh
# cibuildwheel (abbreviated cibw) will take care of building and packaging the Python wheel

set -e

# Find the Python root directory for the current Python version
# This is important for the manylinux infrastructure, which is in
# a nonstandard location that CMake has trouble finding
PYTHON_EXECUTABLE=$(which python3)
echo "Using Python_EXECUTABLE: ${PYTHON_EXECUTABLE}"

# configure for all solvers with permissive licenses (BSD, MIT, etc..)
./configure.sh --bitwuzla --cvc5 --z3 --python --python-executable=${PYTHON_EXECUTABLE}
cd build
make -j
echo "Checking for Z3SolverFactory symbol"
nm -D ./z3/libsmt-switch-z3.so | grep Z3SolverFactory
