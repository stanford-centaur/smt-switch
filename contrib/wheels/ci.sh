#!/usr/bin/env bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
SWITCH_DIR=$DIR/../../

cd $SWITCH_DIR
mkdir -p build
pip install Cython==0.29
python3 contrib/wheels/build_wheel.py bdist_wheel
auditwheel show dist/*
auditwheel repair dist/*
