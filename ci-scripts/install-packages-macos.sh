#!/usr/bin/env bash
set -euo pipefail

brew update
brew install \
  autoconf \
  bison \
  gperf \
  meson \
  python-packaging

{
  echo "CPATH=$(brew --prefix)/include"
  echo "LIBRARY_PATH=$(brew --prefix)/lib"
  echo "PKG_CONFIG_PATH=$(brew --prefix)/lib/pkgconfig"
  echo "PATH=$(brew --prefix bison)/bin:$(brew --prefix)/bin:$PATH"
} >>"$GITHUB_ENV"
