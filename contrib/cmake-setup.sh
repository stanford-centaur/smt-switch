# shellcheck shell=bash
declare -a cmake_options

configure_step() {
  cmake_options+=(
    -DBUILD_SHARED_LIBS=OFF
    -DCMAKE_INSTALL_LIBDIR=lib # keeps libraries out of a lib64 subdirectory
    -DCMAKE_INSTALL_PREFIX="$install_dir"
    -DCMAKE_POLICY_VERSION_MINIMUM=3.10 # CMake < 3.10 is deprecated
    -DCMAKE_POSITION_INDEPENDENT_CODE=ON
  )
  # Each dependency lives under its own prefix, so the search path is a list.
  # CMake wants it semicolon-separated.
  local cmake_prefix_path=
  local prefix
  for prefix in ${dep_prefixes[@]+"${dep_prefixes[@]}"}; do
    cmake_prefix_path+="${cmake_prefix_path:+;}$prefix"
  done
  if [[ -n $cmake_prefix_path ]]; then
    cmake_options+=(-DCMAKE_PREFIX_PATH="$cmake_prefix_path")
  fi
  cmake --no-warn-unused-cli -S . -B build "${cmake_options[@]}"
}

build_step() {
  cmake --build build -j"$num_cores"
}

install_step() {
  cmake --install build
}

_setup_script_path=$(realpath "$0")
# shellcheck source=contrib/common-setup.sh
source "$(dirname "$_setup_script_path")/common-setup.sh"
