#!/usr/bin/env bash
set -euo pipefail

brew update
brew install \
  autoconf \
  bison \
  gperf \
  meson \
  python-packaging
