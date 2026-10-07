#!/usr/bin/env bash
# Downloads the MathSAT release the CI workflow builds against, checks it
# against its recorded SHA-256, and unpacks it into the given directory.

# shellcheck disable=SC2034 # the checksums are read through a built name
set -euo pipefail

version=5.6.18
checksum_linux_aarch64=d7072c9ddeacf3a5cf461876b8d4f544433ae8b171b0eb360c69bfcccc277056
checksum_linux_x86_64=53f9291df410b6899ab12f24c60113a53d7d5f5dcb6e31ba904f08f15c8327f9
checksum_macos=ea98b3cb0de7a6b747f72f468eb4844c9c5d597943a5e73462ac961f73989325

if (($# != 1)); then
  echo "usage: $0 <dir>" >&2
  exit 2
fi
dir=$1

kernel=$(uname -s)
machine=$(uname -m)
case $kernel in
  Darwin) platform=macos ;;
  Linux) platform=linux-$machine ;;
  *) echo "error: no MathSAT build for $kernel" >&2 && exit 2 ;;
esac

checksum_name=checksum_${platform//-/_}
checksum=${!checksum_name-}
if [[ -z $checksum ]]; then
  echo "error: no recorded MathSAT checksum for $platform" >&2
  exit 2
fi

archive=mathsat-$version-$platform.tar.gz
scratch=$(mktemp -d)
trap 'rm -rf "$scratch"' EXIT
curl -fLsS -o "$scratch/$archive" "https://mathsat.fbk.eu/release/$archive"
printf '%s  %s\n' "$checksum" "$scratch/$archive" | shasum -a 256 -c -

mkdir -p "$dir"
tar -xzf "$scratch/$archive" -C "$dir" --strip-components 1
