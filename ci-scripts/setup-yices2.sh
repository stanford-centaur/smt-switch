#!/bin/bash
set -euo pipefail

# requires autoconf, gperf

yices2_version=85cf17e44eac76b5d14b297c09fc9bfecf47ef65 # yices-2.7.0

script_dir=$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)
deps_dir=$script_dir/../deps
# Yices2 is built in its source tree and never installed, so only the source
# half of the prefix layout is populated. See contrib/common-setup.sh.
source_dir=$deps_dir/yices2/src/yices2

kernel_name=$(uname -s)
if [[ $kernel_name == "Darwin" ]]; then
  num_cores=$(sysctl -n hw.logicalcpu)
elif [[ $kernel_name == "Linux" ]]; then
  num_cores=$(nproc)
else
  num_cores=1
fi

if [[ ! -d $source_dir ]]; then
  mkdir -p "$(dirname "$source_dir")"
  git clone https://github.com/SRI-CSL/yices2.git "$source_dir"
  chmod -R 777 "$source_dir"
  cd "$source_dir"
  git checkout -f "$yices2_version"
  autoconf
  ./configure --enable-thread-safety
  make build_dir=build BUILD=build -j"$num_cores"
  cd "$script_dir"
else
  echo "$source_dir already exists." \
    "If you want to rebuild, please remove it manually."
fi

if [[ -f "$source_dir/build/lib/libyices.a" ]]; then
  echo "It appears yices2 was setup successfully into $source_dir."
  echo "You may now install it with" \
    "./configure.sh --yices2 && cd build && make"
else
  echo "Building yices2 failed."
  echo "You might be missing some dependencies."
  echo "Please see their github page for installation instructions:" \
    "https://github.com/SRI-CSL/yices2"
  exit 1
fi
