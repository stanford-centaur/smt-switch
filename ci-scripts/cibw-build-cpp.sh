#!/usr/bin/env bash
# Build the smt-switch C++ libraries for the PyPI release
set -euo pipefail
pip install Cython
./configure.sh --bitwuzla --cvc5 --z3 --python
cmake --build build -j
