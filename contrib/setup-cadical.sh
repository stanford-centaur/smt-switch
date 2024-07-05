#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset

CADICAL_VERSION=rel-1.7.4

SCRIPT_NAME="$(basename "${BASH_SOURCE[0]}")"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
DEPS_DIR="$ROOT_DIR/deps"

# Download
mkdir -p "$DEPS_DIR"
cd $DEPS_DIR
if [[ ! -d "cadical" ]]; then
    git clone https://github.com/arminbiere/cadical
fi

# Build
cd cadical
git checkout $CADICAL_VERSION
if [[ -d "build" ]]; then
    echo "$SCRIPT_NAME: $DEPS_DIR/cadical/build exists, skipping configure step"
else
    CXXFLAGS=-fPIC ./configure
fi
make

# Install
mkdir -p "$DEPS_DIR/install/lib"
install -m644 "build/libcadical.a" "$DEPS_DIR/install/lib"
mkdir -p "$DEPS_DIR/install/include"
install -m644 "src/ccadical.h" "$DEPS_DIR/install/include"
install -m644 "src/cadical.hpp" "$DEPS_DIR/install/include"
