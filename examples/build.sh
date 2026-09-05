#!/usr/bin/env bash
# get the absolute path to this directory
script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"

set -e

help_message() {
  echo "usage: $0 [--python]"
  echo "this script builds smt-switch and the C++ examples"
  echo "it also builds and installs the python bindings if run with --python"
  exit 0
}

if [[ $1 == "--help" ]]; then
  help_message
fi

if [ $# -gt 2 ]; then
  help_message
elif [[ $# -eq 1 && $1 != "--python" ]]; then
  help_message
fi

# go to main repo directory
cd $script_dir/..

# configure and build smt-switch with boolector and cvc5 backends
# set it up to be installed in a directory called example-install in the examples directory
# also use a build directory in the examples directory
./configure.sh --btor --cvc5 --prefix=./examples/example-install --build-dir=$script_dir/example-build $1
cd $script_dir/example-build
make
make test
make install

cd $script_dir
# now make the examples
make

# install python bindings with pip
# this line might need to be adjusted depending on your current python environment
python3 -m pip install -e $script_dir/example-build/python
