#!/usr/bin/env bash
set -e

cd smt-switch/
mkdir -p build
pip install Cython==0.29 --install-option="--no-cython-compile"
python contrib/wheels/build_wheel.py bdist_wheel
auditwheel show dist/*
auditwheel repair dist/*
