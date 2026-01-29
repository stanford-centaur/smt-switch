# shellcheck shell=bash
#
# Can be overridden for projects that don't use GNU autotools.
if ! declare -F configure_step >/dev/null; then
  configure_step() {
    ./configure --prefix "$install_dir"
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
source "$(dirname "$0")/common-setup.sh"
