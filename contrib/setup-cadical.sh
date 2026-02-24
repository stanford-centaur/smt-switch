#!/bin/bash
_version=2.1.3
git_tag=rel-$_version
github_owner=arminbiere

configure_step() {
  ./configure CXXFLAGS="-fPIC"
}

install_step() {
  # Bitwuzla expects the Cadical header to be at include/cadical/cadical.hpp,
  # while Boolector requires include/ccadical.h.
  install_cadical_includedir="$install_includedir/cadical"
  install -d "$install_cadical_includedir" "$install_libdir"
  install -Cm644 src/ccadical.h "$install_includedir"
  install -Cm644 src/cadical.hpp "$install_cadical_includedir"
  install -Cm644 src/tracer.hpp "$install_cadical_includedir"
  install -Cm644 build/libcadical.a "$install_libdir"

  export install_dir _version
  mkdir -p "$install_pkgconfigdir"
  # shellcheck disable=SC2016
  envsubst '$install_dir $_version' <"$pkg_config_dir/cadical.pc.in" >"$install_pkgconfigdir/cadical.pc"
  export -n install_dir _version
}

# shellcheck source=contrib/make-setup.sh
source "$(dirname "$0")/make-setup.sh"
