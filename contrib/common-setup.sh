# shellcheck shell=bash
set -e          # exit on error
set -u          # unset variable raises error
set -o pipefail # exit if an intermediate command in a pipe fails

# Set up paths needed for the rest of the script.
setup_script_path="$(realpath "$0")"
setup_script_name="$(basename "$setup_script_path" .sh)"
dep_name="${setup_script_name##*setup-}" # remove "setup-" from script name
this_script_path="$(realpath "${BASH_SOURCE[0]}")"
contrib_dir="$(dirname "$this_script_path")"
pkg_config_dir="$contrib_dir/pkgconfig"
deps_dir="$(dirname "$contrib_dir")/deps"
install_dir="$deps_dir/install"
install_includedir="$install_dir/include"
install_libdir="$install_dir/lib"
install_pkgconfigdir="$install_libdir/pkgconfig"

# Tell CMake/Meson where the pkg-config files are.
if [[ -z ${PKG_CONFIG_PATH-} ]]; then
  export PKG_CONFIG_PATH="$install_pkgconfigdir"
else
  export PKG_CONFIG_PATH="$install_pkgconfigdir:$PKG_CONFIG_PATH"
fi

# Get the number of CPUs for parallel builds.
if [[ $(uname) == Darwin ]]; then
  num_cores=$(sysctl -n hw.logicalcpu)
elif [[ $(uname -s) =~ Linux* ]]; then
  num_cores="$(nproc)"
else
  num_cores=1
fi

# Check if dependency has already been downloaded.
mkdir -p "$deps_dir" && cd "$deps_dir"
if [[ -d $dep_name ]]; then
  echo "$deps_dir/$dep_name already exists, remove it manually if you want to rebuild $dep_name"
  exit
fi

# Download and unpack archive.
if ! declare -F download_step >/dev/null; then
  download_step() {
    # Set download URL to GitHub by default.
    github_owner="${github_owner:=$dep_name}" # default owner is same as repo name
    github_archive_url="https://github.com/$github_owner/$dep_name/archive"
    if [[ -n ${git_commit-} ]]; then
      source_url="$github_archive_url/$git_commit.tar.gz"
      version="$git_commit"
    elif [[ -n ${git_tag-} ]]; then
      source_url="$github_archive_url/refs/tags/$git_tag.tar.gz"
      version="$git_tag"
    elif [[ -n ${git_branch-} ]]; then
      source_url="$github_archive_url/refs/heads/$git_branch.tar.gz"
      version="$git_branch"
    fi
    dep_filename="$dep_name-$version"
    wget -O "$dep_filename.tar.gz" "$source_url"
    tar -xf "$dep_filename.tar.gz"
    rm "$dep_filename.tar.gz"
    mv "$dep_filename" "$dep_name"
  }
fi
download_step

# Build and install dependency.
cd "$dep_name"
if declare -F prepare_step >/dev/null; then
  prepare_step
fi
configure_step
build_step
install_step
