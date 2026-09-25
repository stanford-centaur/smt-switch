#!/usr/bin/env bash
set -euo pipefail

brew update
brew install \
  autoconf \
  gperf \
  meson \
  python-packaging
