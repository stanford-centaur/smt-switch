#!/bin/bash

# requires autoconf, gperf

yices2_version=98fa2d882d83d32a07d3b8b2c562819e0e0babd0

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
deps_dir=$script_dir/../deps

mkdir -p "$deps_dir"

if [ "$(uname)" == "Darwin" ]; then
  num_cores=$(sysctl -n hw.logicalcpu)
elif [ "$(uname -s)" == "Linux" ]; then
  num_cores=$(nproc)
else
  num_cores=1
fi

if [ ! -d "$deps_dir/yices2" ]; then
  cd "$deps_dir" || exit 1
  git clone https://github.com/SRI-CSL/yices2.git
  chmod -R 777 yices2
  cd yices2 || exit 1
  git checkout -f "$yices2_version"
  autoconf
  ./configure --enable-thread-safety
  make build_dir=build BUILD=build -j"$num_cores"
  cd "$script_dir" || exit 1
else
  echo "$deps_dir/yices2 already exists. If you want to rebuild, please remove it manually."
fi

if [ -f "$deps_dir/yices2/build/lib/libyices.a" ]; then
  echo "It appears yices2 was setup successfully into $deps_dir/yices2."
  echo "You may now install it with make ./configure.sh --yices2 && cd build && make"
else
  echo "Building yices2 failed."
  echo "You might be missing some dependencies."
  echo "Please see their github page for installation instructions: https://github.com/SRI-CSL/yices2"
  exit 1
fi
