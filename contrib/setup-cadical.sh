#!/bin/bash
_version=2.1.3
git_tag=rel-$_version
github_owner=arminbiere

configure_step() {
  ./configure CXXFLAGS="-fPIC"
}

install_step() {
  install -d "$install_includedir" "$install_libdir"
  install -m644 src/ccadical.h "$install_includedir"
  install -m644 src/cadical.hpp "$install_includedir"
  install -m644 src/tracer.hpp "$install_includedir"
  install -m644 build/libcadical.a "$install_libdir"

  export install_dir _version
  mkdir -p "$install_pkgconfigdir"
  # shellcheck disable=SC2016
  envsubst '$install_dir $_version' <"$pkg_config_dir/cadical.pc.in" >"$install_pkgconfigdir/cadical.pc"
  export -n install_dir _version
}

# shellcheck source=contrib/make-setup.sh
source "$(dirname "$0")/make-setup.sh"
