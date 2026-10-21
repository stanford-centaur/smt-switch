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
# Configuring is what provisions them. scikit-build-core builds smt-switch and
# the bindings against them afterwards, once per Python version.
./configure.sh --bitwuzla --cvc5 --z3
