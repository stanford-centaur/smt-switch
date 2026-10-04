#!/usr/bin/env bash
# Prints the cache key for one dependency's build,
# deps-<runner-label>-<prefix>-<hash>, and nothing else on stdout.
#
# Usage: compute-dep-key.sh <runner-label> <prefix>
#
# The hash covers only the files that decide how that one dependency is
# built, so that bumping one solver's pin rebuilds only that solver. The
# label is an argument rather than read from the runner, so that the keys of
# every OS can be computed on any one of them.
#
# Files are hashed whole, comments included: a comment-only edit costs one
# rebuild, and working out which lines matter could miss one.
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

# The installed packages decide what a dependency builds against, and MathSAT
# links against them too.
packages=ci-scripts/install-packages-${label%%-*}.sh
if [[ ! -f $packages ]]; then
  echo "error: there is no $packages for runner label '$label'" >&2
  exit 2
fi

inputs=(ci-scripts/compute-dep-key.sh "$packages")
fields=("label=$label" "prefix=$prefix" "epoch=$epoch")
case $prefix in
  bitwuzla | boolector | cvc5 | yices2 | z3)
    # Named one by one rather than globbed, so that a new file in
    # cmake/provision/ does not silently become an input of every key.
    # refresh-hashes.cmake is left out, as it affects no build.
    inputs+=(
      cmake/ProvisionDeps.cmake
      cmake/provision/CMakeLists.txt
      cmake/provision/Helpers.cmake
      cmake/FindGMP.cmake
      cmake/provision/"$prefix"/*
    )
    ;;
  mathsat)
    # Not provisioned by the build at all; the workflow fetches this release.
    fields+=("msat_version=${MSAT_VERSION:?must be set for mathsat}")
    ;;
  *)
    echo "error: no cache key is defined for prefix '$prefix'" >&2
    exit 2
    ;;
esac

# Hashed into a variable first, so that a failure cannot leave a partial key
# on stdout.
hash=$(
  printf '%s\n' "${fields[@]}"
  sha256sum "${inputs[@]}"
)
hash=$(sha256sum <<<"$hash" | cut -d ' ' -f 1)
echo "deps-$label-$prefix-$hash"
