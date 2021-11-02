#!/usr/bin/env bash
set -e

# This script is meant for running in the keyiz/manylinux docker image
#   see .github/workflows/wheels.yml
# It will create a wheel distribution for PyPi automatically
# manylinux is an old version of Linux (CentOS 6) so that the
# distribution will run on all newer versions

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SWITCH_DIR=$DIR/../../

cd $SWITCH_DIR
mkdir -p build
yum install -y gmp-static libedit-devel
pip install toml setuptools pexpect Cython==0.29
python contrib/wheels/build_wheel.py bdist_wheel
auditwheel show dist/*
auditwheel repair dist/*
pip install ./dist/wheelhouse/*
python3 -c "import smt_switch; print(dir(smt_switch))"
