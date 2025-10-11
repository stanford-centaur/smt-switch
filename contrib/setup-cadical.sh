#!/bin/bash
version_number=2.1.3
git_tag="rel-${version_number}"
github_owner=arminbiere

configure_step() {
  ./configure CXXFLAGS="-fPIC"
}

install_step() {
  install -Dm644 build/libcadical.a "${install_libdir}/libcadical.a"
  install -Dm644 src/cadical.hpp "${install_includedir}/cadical.hpp"
  install -Dm644 src/tracer.hpp "${install_includedir}/tracer.hpp"

  export install_dir version_number
  mkdir -p "${install_pkgconfigdir}"
  envsubst '$install_dir $version_number' < "${pkg_config_dir}/cadical.pc.in" >"${install_pkgconfigdir}}/cadical.pc"
  export -n install_dir version_number
}

source "$(dirname "$0")/make-steps.sh"
source "$(dirname "$0")/common-setup.sh"
