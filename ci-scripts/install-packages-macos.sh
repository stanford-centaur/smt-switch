#!/usr/bin/env bash
set -euo pipefail

brew update
brew install \
  autoconf \
  bison \
  gnu-sed \
  gperf \
  meson \
  python-packaging

{
  echo "LDFLAGS=-L$(brew --prefix)/lib ${LDFLAGS:-}"
  echo "CFLAGS=-I$(brew --prefix)/include ${CFLAGS:-}"
  echo "CPPFLAGS=-I$(brew --prefix)/include ${CPPFLAGS:-}"
  echo "PATH=$(brew --prefix)/opt/bison/bin:$(brew --prefix)/opt/gnu-sed/libexec/gnubin:$PATH"
} >>"$GITHUB_ENV"
