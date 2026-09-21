# shellcheck shell=bash
#
# Several of the variables set below are not read here but by the
# contrib/setup-*.sh front-ends that source this file. shellcheck only looks
# forward from a `source` directive, so it cannot see those uses.
# shellcheck disable=SC2034
#
# Every script in this directory resolves $0 through realpath before taking
# its dirname, both here and in the front-ends that source their library that
# way. That is because ci-scripts/setup-{bitwuzla,btor,cvc5,z3}.sh are symlinks
# into this directory: `dirname "$0"` on its own yields ci-scripts/ and would
# not find the library. realpath is assigned to a variable rather than nested
# inside the source command so that a failure is not swallowed (SC2312).
set -e          # exit on error
set -u          # unset variable raises error
set -o pipefail # exit if an intermediate command in a pipe fails

# Set up paths needed for the rest of the script.
setup_script_path=$(realpath "$0")
setup_script_name=$(basename "$setup_script_path" .sh)
dep_name="${setup_script_name##*setup-}" # remove "setup-" from script name
this_script_path=$(realpath "${BASH_SOURCE[0]}")
contrib_dir=$(dirname "$this_script_path")
deps_dir=$(dirname "$contrib_dir")/deps

# Each dependency gets its own prefix, laid out the way ExternalProject does it
# for a given PREFIX: the tree is installed into <prefix> and the sources sit
# in <prefix>/src/<name>. Keeping to that layout means the eventual move to
# ExternalProject needs no path changes. It also stops a dependency that fails
# halfway from leaving artefacts where the next one's build would find them.
install_dir=$deps_dir/$dep_name
install_includedir=$install_dir/include
install_libdir=$install_dir/lib
download_dir=$install_dir/src
source_dir=$download_dir/$dep_name

# The front-ends declare what they build against in `dependencies`. Stating the
# edges as data rather than as a hand-written prepare_step is what keeps the
# search paths below from drifting away from them. Declaring the array here
# does not disturb a front-end that already filled it in, the same way
# cmake-setup.sh declares cmake_options.
declare -a dependencies
dep_prefixes=()
for dep in ${dependencies[@]+"${dependencies[@]}"}; do
  dep_prefixes+=("$deps_dir/$dep")
done

# Get the number of CPUs for parallel builds.
kernel_name=$(uname -s)
if [[ $kernel_name == Darwin ]]; then
  num_cores=$(sysctl -n hw.logicalcpu)
elif [[ $kernel_name =~ Linux* ]]; then
  num_cores=$(nproc)
else
  num_cores=1
fi

# Build whatever this dependency is built against first. The setup scripts exit
# early when their source tree is already present, so a dependency shared by
# several solvers is built only once.
for dep in ${dependencies[@]+"${dependencies[@]}"}; do
  "$contrib_dir/setup-$dep.sh"
done

# Check if dependency has already been downloaded.
if [[ -d $source_dir ]]; then
  echo "$source_dir already exists," \
    "remove it manually if you want to rebuild $dep_name"
  exit
fi

# Download and unpack archive.
mkdir -p "$download_dir"
cd "$download_dir"
if ! declare -F download_step >/dev/null; then
  download_step() {
    # Set download URL to GitHub by default.
    github_owner="${github_owner:=$dep_name}" # default owner is same as repo name
    github_archive_url=https://github.com/$github_owner/$dep_name/archive
    if [[ -n ${git_commit-} ]]; then
      source_url=$github_archive_url/$git_commit.tar.gz
      version=$git_commit
    elif [[ -n ${git_tag-} ]]; then
      source_url=$github_archive_url/refs/tags/$git_tag.tar.gz
      version=$git_tag
    elif [[ -n ${git_branch-} ]]; then
      source_url=$github_archive_url/refs/heads/$git_branch.tar.gz
      version=$git_branch
    fi
    dep_filename=$dep_name-$version
    wget -4 -O "$dep_filename.tar.gz" "$source_url"
    tar -xf "$dep_filename.tar.gz"
    rm "$dep_filename.tar.gz"
    mv "$dep_filename" "$dep_name"
  }
fi
download_step

# Build and install dependency.
cd "$source_dir"
if declare -F prepare_step >/dev/null; then
  prepare_step
fi
configure_step
build_step
install_step
