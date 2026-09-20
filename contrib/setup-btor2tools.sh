#!/bin/bash
git_commit=d33c73ff1d173f1bfac8ba6b1c6d68ba62c55f8e # 2025-09-18
github_owner=hwmcc

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/cmake-setup.sh
source "$(dirname "$_setup_script_path")/cmake-setup.sh"
