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
  echo "LDFLAGS=-L$(brew --prefix)/lib ${LDFLAGS:-}"
  echo "CFLAGS=-I$(brew --prefix)/include ${CFLAGS:-}"
  echo "CPPFLAGS=-I$(brew --prefix)/include ${CPPFLAGS:-}"
  echo "PATH=$(brew --prefix)/opt/bison/bin:$PATH"
} >>"$GITHUB_ENV"
