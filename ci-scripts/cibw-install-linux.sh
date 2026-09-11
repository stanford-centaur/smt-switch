#!/usr/bin/env bash
set -euo pipefail
dnf install -y \
  cmake \
  gettext \
  glibc-static \
  gperf \
  libstdc++-static \
  ninja-build \
  wget
# ld.gold is too old, so we remove it
rm -f /usr/bin/ld.gold
# Install GMP and MPFR manually, which are too old in the repos
gnu_mirror=https://mirror.us-midwest-1.nexcess.net/gnu
mkdir /tmp/gmp-build
cd /tmp/gmp-build
wget -4 "$gnu_mirror/gmp/gmp-6.3.0.tar.xz" -O gmp.tar.xz
tar -xf gmp.tar.xz --strip-components 1
./configure --enable-cxx
make install
mkdir /tmp/mpfr-build
cd /tmp/mpfr-build
wget -4 "$gnu_mirror/mpfr/mpfr-4.2.2.tar.xz" -O mpfr.tar.xz
tar -xf mpfr.tar.xz --strip-components 1
./configure
make install
rm -r /tmp/{gmp,mpfr}-build
