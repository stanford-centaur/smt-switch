#!/bin/bash
set -euo pipefail

version="5.6.12"

usage() {
  cat <<EOF
Usage: $0 [<option> ...]

Downloads the MathSAT SMT Solver. Note that this solver is under a custom (non-BSD-compliant) license.

-h, --help              display this message and exit
-y, --auto-yes          automatically agree to conditions (default: off)
EOF
  exit 0
}

get_msat=default
while (($# > 0)); do
  case "$1" in
    -h | --help) usage ;;
    -y | --auto-yes) get_msat=y ;;
    *) die "unexpected argument: $1" ;;
  esac
  shift
done

if [[ $get_msat == default ]]; then
  printf "%s\n" "MathSAT is distributed under a custom (non-BSD-compliant) license." \
    "By continuing, you acknowledge this and assume responsibility for meeting the license conditions."
  read -rp "Continue? [y]es/[n]o: " get_msat
fi

if [[ $get_msat != y ]]; then
  echo "Not downloading MathSAT"
  exit 0
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."
mkdir -p deps && cd deps

if [[ -d mathsat ]]; then
  echo "$(pwd)/mathsat already exists. If you want to re-download, please remove it manually."
else
  release_url="https://mathsat.fbk.eu/release"
  if [[ $OSTYPE =~ linux* ]]; then
    wget -O mathsat.tar.gz "${release_url}/mathsat-${version}-linux-x86_64.tar.gz"
  elif [[ $OSTYPE =~ darwin* ]]; then
    wget -O mathsat.tar.gz "${release_url}/mathsat-${version}-macos.tar.gz"
  else
    echo "Unrecognized OSTYPE ${OSTYPE}"
    exit 1
  fi
  mkdir mathsat
  tar -xf mathsat.tar.gz -C mathsat --strip-components 1
  rm mathsat.tar.gz
fi

if [[ ! -f mathsat/lib/libmathsat.a ]]; then
  echo "Downloading mathsat failed."
  exit 1
fi
