# shellcheck shell=bash
declare -a cmake_options

configure_step() {
  cmake_options+=(
    -DBUILD_SHARED_LIBS=OFF
    -DCMAKE_INSTALL_LIBDIR=lib # makes sure libraries go into deps/install/lib
    -DCMAKE_INSTALL_PREFIX="$install_dir"
    -DCMAKE_POLICY_VERSION_MINIMUM=3.10 # CMake < 3.10 is deprecated
    -DCMAKE_POSITION_INDEPENDENT_CODE=ON
    -DCMAKE_PREFIX_PATH="$install_dir"
  )
  cmake --no-warn-unused-cli -S . -B build "${cmake_options[@]}"
}

build_step() {
  cmake --build build -j"$num_cores"
}

install_step() {
  cmake --install build
}

# shellcheck source=contrib/common-setup.sh
source "$(dirname "$(realpath "$0")")/common-setup.sh"
