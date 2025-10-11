#!/bin/bash
set -euo pipefail

script_dir="$(dirname "${BASH_SOURCE[0]}")"
deps_dir="$(dirname "${script_dir}")"

usage() {
  cat <<EOF
Usage: $0 [<option> ...]

Downloads the MathSAT SMT Solver. Note that this solver is under a custom (non BSD compliant) license.

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
  read -rp "MathSAT is distributed under a custom (non-BSD compliant) license. By continuing you acknowledge this distinction and assume responsibility for meeting the license conditions. Continue? [y]es/[n]o: " get_msat
fi

if [[ $get_msat != y ]]; then
  echo "Not downloading MathSAT"
  exit 0
fi

msat_dir="${deps_dir}/mathsat"
version="5.6.12"
release_url="https://mathsat.fbk.eu/release"

if [[ -d $msat_dir ]]; then
  echo "${msat_dir} already exists. If you want to re-download, please remove it manually."
else
  mkdir -p "${msat_dir}"
  cd "${deps_dir}"
  if [[ $OSTYPE =~ linux* ]]; then
    wget -O mathsat.tar.gz "${release_url}/mathsat-${version}-linux-x86_64.tar.gz"
  elif [[ $OSTYPE =~ darwin* ]]; then
    wget -O mathsat.tar.gz "${release_url}/mathsat-${version}-macos-x86_64.tar.gz"
  else
    echo "Unrecognized OSTYPE ${OSTYPE}"
    exit 1
  fi
  tar -xf mathsat.tar.gz -C mathsat --strip-components 1
  rm mathsat.tar.gz
fi

if [[ ! -f "${msat_dir}/lib/libmathsat.a" ]]; then
  echo "Downloading mathsat failed."
  exit 1
fi
