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

# Build and install GMP and MPFR, which are too old in the repos
mkdir -p deps && pushd deps
wget https://ftpmirror.gnu.org/gmp/gmp-6.3.0.tar.xz
tar -xf gmp-6.3.0.tar.xz && mv gmp-6.3.0 gmp && rm -f gmp-6.3.0.tar.xz
pushd gmp && ./configure && make install && popd
wget https://ftpmirror.gnu.org/mpfr/mpfr-4.2.2.tar.xz
tar -xf mpfr-4.2.2.tar.xz && mv mpfr-4.2.2 mpfr && rm -f mpfr-4.2.2.tar.xz
cd mpfr && ./configure && make install && popd

python3 -m venv ./build-deps-env
source ./build-deps-env/bin/activate
python3 -m pip install meson pyparsing tomli

./contrib/setup-bitwuzla.sh
# the version of ld.gold is too old in manylinux_2_28, remove it so cvc5 falls back on bfd
rm -f /usr/bin/ld.gold
source ./build-deps-env/bin/activate
./contrib/setup-cvc5.sh
./contrib/setup-z3.sh
