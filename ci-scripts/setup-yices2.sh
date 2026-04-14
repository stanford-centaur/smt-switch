#!/usr/bin/env bash
# requires autoconf, gperf
git_commit=98fa2d882d83d32a07d3b8b2c562819e0e0babd0
github_owner=SRI-CSL
configure_opts=(--enable-thread-safety)

prepare_step() {
  autoconf
}

# shellcheck source=contrib/make-setup.sh
source "$(dirname "$(dirname "$0")")/contrib/make-setup.sh"
