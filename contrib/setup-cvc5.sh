#!/bin/bash
git_commit=b432cd77ebeb41091de42637ca8523f8437a1db1 # cvc5-1.4.0
cmake_options=(-DENABLE_AUTO_DOWNLOAD=ON -DUSE_POLY=ON)
dependencies=(cadical)

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$_setup_script_path")/cmake-setup.sh"
