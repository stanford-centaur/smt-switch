#!/usr/bin/env bash
set -euo pipefail

sudo apt-get update
sudo apt-get install -y \
  gperf \
  libmpfr-dev \
  meson \
  python3-packaging
