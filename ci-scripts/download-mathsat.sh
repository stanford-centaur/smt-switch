#!/usr/bin/env bash
# Downloads the MathSAT release the CI workflow builds against, checks it
# against its recorded SHA-256, and unpacks it into the given directory.

# shellcheck disable=SC2034 # the checksums are read through a built name
set -euo pipefail

version=5.6.20
checksum_linux_aarch64=38e96b8fb5a62f633cfaa1d4937f76d4d8156bd9a785e30ea12724110d75b589
checksum_linux_x86_64=ca7d91b39b9934a00c4410057076c5a5029836a8a693206bfbbc968c52daa91e
checksum_macos=3a0c034bbb4efe31fea3c09e8cd140110a52dd596a9bfa9a27c5e84f420bfe92

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
