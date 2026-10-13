#!/usr/bin/env bash
# Downloads the MathSAT release the CI workflow builds against, checks it
# against its recorded SHA-256, and unpacks it into the given directory.

# shellcheck disable=SC2034 # the checksums are read through a built name
set -euo pipefail

version=5.6.19
checksum_linux_aarch64=0bcae6ffd247736db17a7856a1fc6f3a76774a32baf86ebd33f0e778256a9af5
checksum_linux_x86_64=c56f755851de017104e8fc7aac6677d90bf310448a750140ee9f2630a7c4f4c5
checksum_macos=d71f93afe13d94bcfc58bedcc4fc6ff4697414df1ba951b09deb66baf1de62c7

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
