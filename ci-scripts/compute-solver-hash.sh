#!/usr/bin/env bash
set -euo pipefail
gethash() {
  sha256sum "$1" | cut -d ' ' -f 1
}
solver="$1"
solver_hash="$(gethash ci-scripts/setup-"$1".sh)"
if [[ $solver == bitwuzla || $solver == btor || $solver == cvc5 || $solver == z3 ]]; then
  solver_hash+="$(gethash contrib/common-setup.sh)"
  if [[ $solver == bitwuzla ]]; then
    solver_hash+="$(gethash contrib/meson-setup.sh)"
  else
    solver_hash+="$(gethash contrib/cmake-setup.sh)"
  fi
  if [[ $solver != z3 ]]; then
    solver_hash+="$(gethash contrib/setup-cadical.sh)"
    solver_hash+="$(gethash contrib/make-setup.sh)"
    solver_hash+="$(gethash contrib/pkgconfig/cadical.pc.in)"
  fi
fi
if [[ $solver == btor ]]; then
  solver_hash+="$(gethash contrib/setup-btor2tools.sh)"
fi
echo "result=$(gethash <(echo "$solver_hash"))" >>"$GITHUB_OUTPUT"
