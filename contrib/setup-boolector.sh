#!/bin/bash
git_tag=3.2.4
cmake_options=(-DUSE_CADICAL=ON)
dependencies=(cadical btor2tools)

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$_setup_script_path")/cmake-setup.sh"
