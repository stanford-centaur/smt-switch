# shellcheck shell=bash
declare -a meson_setup_options meson_compile_options

# Can be overridden for projects that provide a custom config script.
if ! declare -F configure_step >/dev/null; then
  configure_step() {
    meson_setup_options+=(
      -Dprefix="$install_dir"
    )
    meson setup build "${meson_setup_options[@]}"
  }
fi

build_step() {
  meson compile -C build ${meson_compile_options[@]+"${meson_compile_options[@]}"}
}

install_step() {
  meson install -C build
}

# shellcheck source=contrib/common-setup.sh
source "$(dirname "$(realpath "$0")")/common-setup.sh"
