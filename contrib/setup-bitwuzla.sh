#!/bin/bash
git_commit=532ca9729136969008960481167ab55696a9cc52

prepare_step() {
  "$contrib_dir/setup-cadical.sh"
}

source "$(dirname "$(realpath "$0")")/meson-steps.sh"
source "$(dirname "$(realpath "$0")")/common-setup.sh"
