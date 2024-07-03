#!/bin/bash
set -o errexit
set -o pipefail
set -o nounset

CADICAL_VERSION=rel-1.7.4

SCRIPT_NAME="$(basename "${BASH_SOURCE[0]}")"
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ROOT_DIR="$(cd "$SCRIPT_DIR/.." && pwd)"
DEPS_DIR="$ROOT_DIR/deps"

mkdir -p "$DEPS_DIR"
cd $DEPS_DIR
if [[ ! -d "cadical" ]]; then
    git clone https://github.com/arminbiere/cadical
fi
cd cadical
git checkout $CADICAL_VERSION
if [[ -d "build" ]]; then
    echo "$SCRIPT_NAME: $DEPS_DIR/cadical/build exists, skipping configure step"
else
    CXXFLAGS=-fPIC ./configure
fi
make
install -Dm644 -t "$DEPS_DIR/install/lib" "build/libcadical.a"
