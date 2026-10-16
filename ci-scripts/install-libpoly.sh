#!/usr/bin/env bash
# Builds and installs LibPoly with its position-independent archives, picpoly
# and picpolyxx, which a static cvc5 links, so that cvc5 uses this LibPoly
# rather than downloading one of its own. The packaging on both platforms
# turns those archives off, so it is patched before it builds: on Ubuntu,
# the Debian packaging in LibPoly's own repository, as SRI-CSL's PPA has
# LibPoly 0.2.0 only, older than the 0.2.1 cvc5 requires; on macOS,
# SRI-CSL's formula, from their tap.
set -euo pipefail

tag=v0.2.1
flag_off=-DLIBPOLY_BUILD_STATIC_PIC=OFF
flag_on=-DLIBPOLY_BUILD_STATIC_PIC=ON

# Turns the archives on in the given packaging file, and fails if the file
# no longer has the flag to turn. -i takes a suffix to work with both GNU and
# BSD sed.
enable_pic() {
  sed -i.orig "s/$flag_off/$flag_on/" "$1"
  rm "$1.orig"
  grep -q -- "$flag_on" "$1"
}

kernel=$(uname -s)
case $kernel in
  Linux)
    work=$(mktemp -d)
    git clone --quiet --depth 1 --branch "$tag" \
      https://github.com/SRI-CSL/libpoly.git "$work/libpoly"
    enable_pic "$work/libpoly/debian/rules"
    # dpkg-buildpackage writes the packages beside the source tree. -d skips
    # its check of the build dependencies, which counts only packages apt
    # installed, while the runner's cmake comes from elsewhere.
    (cd "$work/libpoly" && dpkg-buildpackage --build=binary -us -uc -d)
    sudo apt-get install --no-install-recommends \
      "$work"/libpoly0_*.deb "$work"/libpoly-dev_*.deb
    ;;
  Darwin)
    # A tap's formula is read from its local clone, which nothing updates
    # while HOMEBREW_NO_AUTO_UPDATE is set, so the patched copy is built.
    brew tap SRI-CSL/sri-csl
    formula=$(brew --repository SRI-CSL/sri-csl)/Formula/libpoly.rb
    enable_pic "$formula"
    # the cache keys know the tag, not what the tap builds, so a tap that
    # moved on has to stop the build
    grep -q "url \".*/$tag.tar.gz\"" "$formula"
    brew install --build-from-source SRI-CSL/sri-csl/libpoly
    ;;
  *) echo "error: no LibPoly build for $kernel" >&2 && exit 2 ;;
esac
