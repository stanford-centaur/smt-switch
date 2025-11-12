#!/bin/echo Script should be sourced from contrib/setup-xxx.sh, not executed directly:
set -e  # exit on error
set -u  # unset variable raises error

# Set up paths needed for the rest of the script.
setup_script_path="$(realpath "$0")"
contrib_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
smt_switch_dir="$(dirname "$contrib_dir")"
deps_dir="$smt_switch_dir/deps"
install_dir="$deps_dir/install"
install_libdir="$install_dir/lib"
install_includedir="$install_dir/include"

# Tell CMake/Meson where the pkg-config files are.
pkg_config_dir="$install_libdir/pkgconfig"
if [ -z "${PKG_CONFIG_PATH-}" ]; then
  export PKG_CONFIG_PATH="$pkg_config_dir"
else
  export PKG_CONFIG_PATH="$pkg_config_dir:$PKG_CONFIG_PATH"
fi

# Get the number of CPUs for parallel builds.
if [ "$(uname)" == "Darwin" ]; then
  num_cores=$(sysctl -n hw.logicalcpu)
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
  num_cores=$(nproc)
else
  num_cores=1
fi

# Create directories under deps/.
mkdir -p "$pkg_config_dir" "$install_includedir"

cd "$deps_dir"

# Determine the name of the dependency we are building.
setup_script_name="$(basename "$setup_script_path" .sh)"
dep_name=${setup_script_name##*setup-}  # remove "setup-" from script name

if [ -d $dep_name ]; then
  echo "$deps_dir/$dep_name already exists, remove it manually if you want to rebuild $dep_name"
  exit
fi

# Set download URL to GitHub by default.
github_owner=${github_owner:=$dep_name}  # default owner is same as repo name
github_archive_url=https://github.com/$github_owner/$dep_name/archive
if [ -n "${git_commit-}" ]; then
  url=$github_archive_url/$git_commit.tar.gz
  version=${version:=$git_commit}
elif [ -n "${git_tag-}" ]; then
  url=$github_archive_url/refs/tags/$git_tag.tar.gz
  version=${version:=$git_tag}
elif [ -n "${git_branch-}" ]; then
  url=$github_archive_url/refs/heads/$git_branch.tar.gz
  version=${version:=$git_branch}
fi

# Download and unpack archive.
if declare -F download_step >/dev/null; then
  download_step
else
  filename=$dep_name-$version
  curl -L "$url" -o $filename.tar.gz
  tar -xf $filename.tar.gz
  rm $filename.tar.gz
  mv $filename $dep_name
fi

cd $dep_name

if declare -F prepare_step >/dev/null; then
  prepare_step
fi
configure_step
build_step
install_step
