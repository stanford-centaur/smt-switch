#!/bin/bash
set -e

BITWUZLA_VERSION=532ca9729136969008960481167ab55696a9cc52
CONTRIB_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
SOURCE_DIR="$(dirname "$CONTRIB_DIR")"
DEPS_DIR="$SOURCE_DIR/deps"
INSTALL_DIR="$DEPS_DIR/install"

mkdir -p "$DEPS_DIR" && cd "$DEPS_DIR"

if [ ! -d bitwuzla ]; then
    "$CONTRIB_DIR/setup-cadical.sh"
    git clone https://github.com/bitwuzla/bitwuzla.git && cd bitwuzla
    git checkout -f $BITWUZLA_VERSION
    export CPLUS_INCLUDE_PATH="$INSTALL_DIR/include" LIBRARY_PATH="$INSTALL_DIR/lib"
    ./configure.py --prefix "$INSTALL_DIR" && cd build
    meson configure -Dlibdir=lib  # makes sure libraries go into deps/install/lib
    meson compile
    meson install
else
    echo "$DEPS_DIR/bitwuzla already exists. If you want to rebuild, please remove it manually."
fi
