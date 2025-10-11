set -e  # exit on error
set -u  # unset variable raises error
set -o pipefail # exit if an intermediate command in a pipe fails

# Set up paths needed for the rest of the script.
setup_script_path="$(realpath "$0")"
contrib_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" >/dev/null 2>&1 && pwd)"
pkg_config_dir="${contrib_dir}/pkgconfig"
smt_switch_dir="$(dirname "${contrib_dir}")"
deps_dir="${smt_switch_dir}/deps"
install_dir="${deps_dir}/install"
install_libdir="${install_dir}/lib"
install_includedir="${install_dir}/include"
install_pkgconfigdir="${install_libdir}/pkgconfig"

# Tell CMake/Meson where the pkg-config files are.
if [[ -z "${PKG_CONFIG_PATH-}" ]]; then
  export PKG_CONFIG_PATH="${install_pkgconfigdir}"
else
  export PKG_CONFIG_PATH="${install_pkgconfigdir}:${PKG_CONFIG_PATH}"
fi

# Get the number of CPUs for parallel builds.
if [[ "$(uname)" == Darwin ]]; then
  num_cores=$(sysctl -n hw.logicalcpu)
elif [[ "$(uname -s)" =~ Linux* ]]; then
  num_cores="$(nproc)"
else
  num_cores=1
fi

# Determine the name of the dependency we are building.
setup_script_name="$(basename "${setup_script_path}" .sh)"
dep_name="${setup_script_name##*setup-}"  # remove "setup-" from script name
dep_dir="${deps_dir}/${dep_name}"

# Check if dependency has already been downloaded.
if [[ -d "${dep_dir}" ]]; then
  echo "${dep_dir} already exists, remove it manually if you want to rebuild ${dep_name}"
  exit
fi

# Set download URL to GitHub by default.
github_owner="${github_owner:=${dep_name}}"  # default owner is same as repo name
github_archive_url="https://github.com/${github_owner}/${dep_name}/archive"
if [[ -n "${git_commit-}" ]]; then
  source_url="${github_archive_url}/${git_commit}.tar.gz"
  dep_version="${version:=${git_commit}}"
elif [[ -n "${git_tag-}" ]]; then
  source_url="${github_archive_url}/refs/tags/${git_tag}.tar.gz"
  dep_version="${version:=${git_tag}}"
elif [[ -n "${git_branch-}" ]]; then
  source_url="${github_archive_url}/refs/heads/${git_branch}.tar.gz"
  dep_version="${version:=${git_branch}}"
fi

# Download and unpack archive.
mkdir -p "${deps_dir}"
cd "${deps_dir}"
if declare -F download_step >/dev/null; then
  download_step
else
  dep_filename="${dep_name}-${dep_version}"
  wget -O "${dep_filename}.tar.gz" "${source_url}"
  tar -xf "${dep_filename}.tar.gz"
  rm "${dep_filename}.tar.gz"
  mv "${dep_filename}" "${dep_name}"
fi

# Build and install dependency.
cd "${dep_dir}"
if declare -F prepare_step >/dev/null; then
  prepare_step
fi
configure_step
build_step
install_step
