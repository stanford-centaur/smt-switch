#!/usr/bin/env bash
# Installs the libraries that solvers link but Ubuntu does not package as
# they need, from the Debian packages in $EXTRA_LIBRARIES_DIR, after building
# them there if it holds none. CI caches that directory, so they are only
# built again when this script or vars.sh changes.
#
# LibPoly, which cvc5 links and Yices2 needs for MCSAT, is built from the
# Debian packaging in its own repository, as SRI-CSL's PPA has LibPoly 0.2.0
# only, older than the 0.2.1 cvc5 requires. That packaging turns off the
# position-independent archives, picpoly and picpolyxx, which a static cvc5
# links, so it is patched to build them, and cvc5 then uses this LibPoly
# rather than downloading one of its own. CUDD, which MCSAT needs as well,
# is the PPA's as it is.
set -euo pipefail
# shellcheck source=vars.sh
source "$(dirname "$0")/vars.sh"

build() {
  sudo add-apt-repository --yes ppa:sri-csl/formal-methods
  (cd "$EXTRA_LIBRARIES_DIR" && apt-get download cudd)
  # dpkg-buildpackage needs these; dh-exec brings debhelper with it
  sudo apt-get install --no-install-recommends dh-exec fakeroot
  local work
  work=$(mktemp -d)
  git clone --quiet --depth 1 --branch "$LIBPOLY_TAG" \
    https://github.com/SRI-CSL/libpoly.git "$work/libpoly"
  # fails if the packaging no longer has the option to turn on
  local rules=$work/libpoly/debian/rules
  sed -i "s/$LIBPOLY_PIC_OPTION=OFF/$LIBPOLY_PIC_OPTION=ON/" "$rules"
  grep -q -- "$LIBPOLY_PIC_OPTION=ON" "$rules"
  # dpkg-buildpackage writes the packages beside the source tree. -d skips
  # its check of the build dependencies, which counts only packages apt
  # installed, while the runner's cmake comes from elsewhere.
  (cd "$work/libpoly" && dpkg-buildpackage --build=binary -us -uc -d)
  mv "$work"/libpoly0_*.deb "$work"/libpoly-dev_*.deb "$EXTRA_LIBRARIES_DIR"
}

mkdir -p "$EXTRA_LIBRARIES_DIR"
if ! compgen -G "$EXTRA_LIBRARIES_DIR/*.deb" >/dev/null; then
  build
fi
sudo apt-get install --no-install-recommends "$EXTRA_LIBRARIES_DIR"/*.deb
