#!/usr/bin/env bash
# Build all permissively licensed solvers for the PyPi release
set -euo pipefail
python -m venv buildenv
# shellcheck source=/dev/null  # activate script created by the command above
source buildenv/bin/activate
pip install \
  meson \
  pyparsing \
  tomli
contrib/setup-bitwuzla.sh
contrib/setup-cvc5.sh
contrib/setup-z3.sh
