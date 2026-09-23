#!/usr/bin/env bash
set -euo pipefail

brew update
brew install \
  autoconf \
  gperf \
  meson \
  python-packaging

brew_prefix=$(brew --prefix)

{
  echo "CPATH=$brew_prefix/include"
  echo "LIBRARY_PATH=$brew_prefix/lib"
  echo "PKG_CONFIG_PATH=$brew_prefix/lib/pkgconfig"
} >>"${GITHUB_ENV:?}"
