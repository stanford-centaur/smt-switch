#!/bin/bash
git_commit=fb69ee3b95e8baa5f0a9a6b0b19ee8beaad52932
github_owner=hwmcc

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$_setup_script_path")/cmake-setup.sh"
