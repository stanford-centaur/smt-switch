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
# This script builds all the permissive-license solvers that can be included
# in the PyPi release.

set -e

python3 -m venv ./build-deps-env
source ./build-deps-env/bin/activate
python3 -m pip install meson setuptools pyparsing toml tomli

./contrib/setup-bitwuzla.sh
# the version of ld.gold is too old in manylinux_2_28, remove it so cvc5 falls back on bfd
rm -f /usr/bin/ld.gold
source ./build-deps-env/bin/activate
./contrib/setup-cvc5.sh
./contrib/setup-z3.sh
