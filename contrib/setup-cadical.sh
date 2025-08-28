#!/bin/bash
git_tag=rel-2.1.3
github_owner=arminbiere

configure_step() {
  ./configure CXXFLAGS="-fPIC"
}

install_step() {
  install -m644 build/libcadical.a "$install_libdir"
  install -m644 src/ccadical.h "$install_includedir"
  install -m644 src/cadical.hpp "$install_includedir"
  install -m644 src/tracer.hpp "$install_includedir"
}

source "$(dirname "$0")/make-steps.sh"
source "$(dirname "$0")/common-setup.sh"
