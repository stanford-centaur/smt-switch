#!/bin/bash
git_tag=cvc5-1.3.4
cmake_options=(-DENABLE_AUTO_DOWNLOAD=ON -DUSE_POLY=ON)
dependencies=(cadical)

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$_setup_script_path")/cmake-setup.sh"
