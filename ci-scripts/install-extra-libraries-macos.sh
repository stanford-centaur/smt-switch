#!/usr/bin/env bash
# Installs the libraries that solvers link but Homebrew does not package as
# they need, from the Homebrew kegs in $EXTRA_LIBRARIES_DIR, after building
# them and keeping their kegs there if it holds none. CI caches that
# directory, so they are only built again when this script or vars.sh
# changes. Bottles would be the usual way to keep a build, but Homebrew
# refuses to install one from a file unless HOMEBREW_DEVELOPER is set.
#
# LibPoly, which cvc5 links and Yices2 needs for MCSAT, is built from
# SRI-CSL's formula, from their tap. That formula turns off the
# position-independent archives, picpoly and picpolyxx, which a static cvc5
# links, so it is patched to build them, and cvc5 then uses this LibPoly
# rather than downloading one of its own. CUDD, which MCSAT needs as well,
# is the tap's as it is.
set -euo pipefail
# shellcheck source=vars.sh
source "$(dirname "$0")/vars.sh"

build() {
  # A tap's formula is read from its local clone, which nothing updates
  # while HOMEBREW_NO_AUTO_UPDATE is set, so the patched copy is built.
  local formula
  formula=$(brew --repository SRI-CSL/sri-csl)/Formula/libpoly.rb
  # fails if the formula no longer has the option to turn on
  sed -i '' "s/$LIBPOLY_PIC_OPTION=OFF/$LIBPOLY_PIC_OPTION=ON/" "$formula"
  grep -q -- "$LIBPOLY_PIC_OPTION=ON" "$formula"
  # the cache keys know LIBPOLY_TAG, not what the tap builds, so a tap that
  # moved on has to stop the build
  grep -q "url \".*/$LIBPOLY_TAG.tar.gz\"" "$formula"
  brew install --build-from-source \
    SRI-CSL/sri-csl/cudd SRI-CSL/sri-csl/libpoly
  cp -R "$cellar/cudd" "$cellar/libpoly" "$EXTRA_LIBRARIES_DIR"
}

mkdir -p "$EXTRA_LIBRARIES_DIR"
brew tap SRI-CSL/sri-csl
# Homebrew before 6.0.0 has no tap trust, and loads any tap's formulae
if brew commands --quiet | grep -x trust >/dev/null; then
  brew trust --tap SRI-CSL/sri-csl
fi
cellar=$(brew --cellar)
if [[ -d $EXTRA_LIBRARIES_DIR/libpoly ]]; then
  # LibPoly links GMP, which installing the formula would have brought
  brew install gmp
  cp -R "$EXTRA_LIBRARIES_DIR/cudd" "$EXTRA_LIBRARIES_DIR/libpoly" "$cellar"
  brew link cudd libpoly
else
  build
fi
