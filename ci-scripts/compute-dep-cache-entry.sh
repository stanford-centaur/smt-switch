#!/usr/bin/env bash
# Prints the cache entry for one dependency's build as one line of JSON,
# {"key": ..., "path": ...}. The key is deps-<runner-label>-<prefix>-<hash>,
# the path is what actions/cache takes, one path per line.
#
# Usage: compute-dep-cache-entry.sh <runner-label> <prefix>
#
# The hash covers only the files that decide how that one dependency is
# built, so that bumping one solver's pin rebuilds only that solver. The
# label is an argument rather than read from the runner, so that the entries
# of every OS can be computed on any one of them.
set -euo pipefail
# Fixes the order the recipe directory's glob expands in
export LC_ALL=C

if (($# != 2)); then
  echo "usage: $0 <runner-label> <prefix>" >&2
  exit 2
fi
label=$1
prefix=$2
# Bumped by hand to rebuild every cached dependency
epoch=${DEPS_CACHE_EPOCH:?must be set, as it is by the workflow}

cd "$(dirname "$0")/.."

# The installed packages decide what a dependency builds or links against.
case $label in
  ubuntu-*) packages=${APT_PACKAGES:?must be set, as it is by the workflow} ;;
  macos-*) packages=${BREW_PACKAGES:?must be set, as it is by the workflow} ;;
  *) echo "error: no package list for runner label '$label'" >&2 && exit 2 ;;
esac

inputs=(ci-scripts/compute-dep-cache-entry.sh)
fields=("label=$label" "prefix=$prefix" "epoch=$epoch" "packages=$packages")
path=deps/$prefix
if [[ $prefix == mathsat ]]; then
  # Not provisioned by the build at all; the workflow runs this script, which
  # holds the version and the checksums. It unpacks the release into the
  # path, which therefore has to stay one directory.
  inputs+=(ci-scripts/download-mathsat.sh)
elif [[ -d cmake/provision/$prefix ]]; then
  inputs+=(
    cmake/ProvisionDeps.cmake
    cmake/provision/CMakeLists.txt
    cmake/provision/Helpers.cmake
    cmake/FindGMP.cmake
    cmake/provision/"$prefix"/*
  )
  # Bitwuzla is built with the meson that the requirements pin
  if [[ $prefix == bitwuzla ]]; then
    inputs+=(ci-scripts/requirements.txt)
  fi
  # The sources and build trees under src/ are most of a prefix's size, and
  # nothing reads them once the dependency is installed. Boolector is the
  # exception: its backend includes Boolector's private headers from there,
  # and its package names the CaDiCaL and btor2tools built there by path.
  if [[ $prefix != boolector ]]; then
    path+=$'\n'"!deps/$prefix/src"
  fi
else
  echo "error: '$prefix' is neither mathsat nor in cmake/provision/" >&2
  exit 2
fi

hash=$(
  printf '%s\n' "${fields[@]}"
  sha256sum "${inputs[@]}"
)
hash=$(sha256sum <<<"$hash" | cut -d ' ' -f 1)
jq -cn --arg key "deps-$label-$prefix-$hash" --arg path "$path" \
  '{key: $key, path: $path}'
