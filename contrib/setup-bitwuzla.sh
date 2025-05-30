#!/bin/bash
git_commit=532ca9729136969008960481167ab55696a9cc52

source "$(dirname "$(realpath "$0")")/common-setup.sh"

"$contrib_dir/setup-cadical.sh"

./configure.py --prefix "$install_dir"
meson configure build -Dlibdir=lib  # makes sure libraries go into deps/install/lib
meson compile -C build
meson install -C build
