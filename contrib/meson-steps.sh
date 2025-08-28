#!/bin/echo Script should be sourced from contrib/setup-xxx.sh, not executed directly:
declare -a meson_setup_options meson_compile_options

configure_step() {
  meson_setup_options+=(
    -Dlibdir=lib  # makes sure libraries go into deps/install/lib
    -Dprefix="$install_dir"
  )
  meson setup build "${meson_setup_options[@]}"
}

build_step() {
  meson compile -C build ${meson_compile_options[@]+"${meson_compile_options[@]}"}
}

install_step() {
  meson install -C build
}
