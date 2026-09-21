#!/usr/bin/env bash
# Build all permissively licensed solvers for the PyPi release
set -euo pipefail
python -m venv buildenv
# shellcheck source=/dev/null  # activate script created by the command above
source buildenv/bin/activate
# Bitwuzla's configure.py drives Meson, which is not a system package here.
pip install \
  meson \
  pyparsing \
  tomli
# Configuring is what provisions them; the C++ build itself is a separate step
# so that this one can be cached on its own.
./configure.sh --bitwuzla --cvc5 --z3
