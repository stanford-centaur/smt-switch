# shellcheck shell=bash
declare -a configure_opts

# Can be overridden for projects that don't use GNU autotools.
if ! declare -F configure_step >/dev/null; then
  configure_step() {
    configure_opts+=(--prefix "$install_dir")
    ./configure "${configure_opts[@]}"
  }
fi

build_step() {
  make -j"$num_cores"
}

# Can be overridden for projects without an install target.
if ! declare -F install_step >/dev/null; then
  install_step() {
    make install
  }
fi

# shellcheck source=contrib/common-setup.sh
source "$(dirname "${BASH_SOURCE[0]}")/common-setup.sh"
