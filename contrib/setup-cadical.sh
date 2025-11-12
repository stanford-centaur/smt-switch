#!/bin/bash
version_number=2.1.3
git_tag=rel-$version_number
github_owner=arminbiere

configure_step() {
  ./configure CXXFLAGS="-fPIC"
}

install_step() {
  install -m644 build/libcadical.a "$install_libdir"
  install -m644 src/ccadical.h "$install_includedir"
  install -m644 src/cadical.hpp "$install_includedir"
  install -m644 src/tracer.hpp "$install_includedir"

  export install_dir version_number
  envsubst '$install_dir $version_number' <"$contrib_dir/pkgconfig/cadical.pc.in" >"$pkg_config_dir/cadical.pc"
  export -n install_dir version_number
}

source "$(dirname "$0")/make-steps.sh"
source "$(dirname "$0")/common-setup.sh"
