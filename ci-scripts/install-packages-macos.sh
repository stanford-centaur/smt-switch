#!/usr/bin/env bash
set -euo pipefail

brew update
brew install \
  autoconf \
  bison \
  gperf \
  meson \
  python-packaging

brew_prefix=$(brew --prefix)
bison_prefix=$(brew --prefix bison)

{
  echo "CPATH=$brew_prefix/include"
  echo "LIBRARY_PATH=$brew_prefix/lib"
  echo "PKG_CONFIG_PATH=$brew_prefix/lib/pkgconfig"
  echo "PATH=$bison_prefix/bin:$brew_prefix/bin:$PATH"
} >>"${GITHUB_ENV:?}"
