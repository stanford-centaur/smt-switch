#!/usr/bin/env bash
set -euo pipefail
gethash() {
  sha256sum "$1" | cut -d ' ' -f 1
}
solver=$1
# Seeded with the solver name so that each one keeps its own cache entry. The
# cache holds all of deps/, so a key shared between two solvers would let the
# second get a hit on a tree its own solver is missing from -- and, having
# hit, never save it.
solver_hash=$solver
# The installed packages decide what the solver builds against
# shellcheck disable=SC2154 # RUNNER_LABEL is set by the workflow
solver_hash+=$(gethash ci-scripts/install-packages-"${RUNNER_LABEL%%-*}".sh)
if [[ $solver == msat ]]; then
  # The one solver still installed by a script of its own.
  solver_hash+=$(gethash ci-scripts/setup-msat.sh)
else
  # Everything else is provisioned by the CMake driver. Hashing all of it
  # rather than working out which recipes a given solver pulls in costs an
  # occasional unnecessary rebuild and cannot miss one.
  for file in cmake/ProvisionDeps.cmake cmake/provision/*; do
    if [[ -f $file ]]; then
      solver_hash+=$(gethash "$file")
    fi
  done
fi
result=$(gethash <(echo "$solver_hash"))
echo "result=$result" >>"${GITHUB_OUTPUT:?}"
