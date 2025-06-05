#!/bin/echo Script should be sourced from contrib/setup-xxx.sh, not executed directly:
declare -a cmake_options

configure_step() {
  cmake_options+=(
    -DBUILD_SHARED_LIBS=OFF
    -DCMAKE_INSTALL_LIBDIR=lib # makes sure libraries go into deps/install/lib
    -DCMAKE_INSTALL_PREFIX="$install_dir"
    -DCMAKE_POLICY_VERSION_MINIMUM=3.5  # CMake 4.0 and later require 3.5 at minimum
    -DCMAKE_POSITION_INDEPENDENT_CODE=ON
    -DCMAKE_PREFIX_PATH="$install_dir"
  )
  cmake -S . -B build "${cmake_options[@]}"
}

build_step() {
  cmake --build build -j$num_cores
}

install_step() {
  cmake --install build
}
