#!/bin/echo Script should be sourced from contrib/setup-xxx.sh, not executed directly:
declare -a meson_options

configure_step() {
  meson_options+=(
    -Dlibdir=lib  # makes sure libraries go into deps/install/lib
    -Dprefix="$install_dir"
  )
  meson setup build "${meson_options[@]}"
}

build_step() {
  meson compile -C build
}

install_step() {
  meson install -C build
}
