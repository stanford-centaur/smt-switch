#!/bin/sh

# Syntax and structure borrowed from CVC5's configure.sh script

usage() {
  cat <<EOF
Usage: $0 [<option> ...]

Configures the CMAKE build environment.

-h, --help              display this message and exit
--prefix=STR            install directory       (default: /usr/local/)
--btor                  build boolector         (default: off)
--bitwuzla              build bitwuzla            (default: off)
--cvc5                  build cvc5              (default: off)
--msat                  build MathSAT           (default: off)
--yices2                build yices2            (default: off)
--z3                    build z3                (default: off)
--btor-dir=STR          custom Boolector install prefix (default: deps/boolector)
--btor-src-dir=STR      custom Boolector source tree    (default: <btor-dir>/src/boolector)
--cvc5-dir=STR          custom cvc5 install prefix      (default: deps/cvc5)
--msat-dir=STR          custom MathSAT install prefix   (default: deps/mathsat)
--yices2-dir=STR        custom Yices2 install prefix    (default: deps/yices2)
--build-dir=STR         custom build directory  (default: build)
--static                create static libraries (default: off)
--no-auto-deps          do not build dependencies that cannot be found (default: off)
--allow-gpl             permit downloading GPL dependencies, i.e. yices2 (default: off)
--without-tests         build without the smt-switch test suite (default: off)
--no-system-gtest       do not use system GTest sources; forces download (default: off)
--python                compile with python bindings (default: off)
--python-executabe      point to a particular Python interpreter - will look around this for include and lib dirs
--smtlib-reader         include the smt-lib reader - requires bison/flex (default:off)
--bison-dir=STR         custom bison install prefix     (default: deps/bison)
--flex-dir=STR          custom flex install prefix      (default: deps/flex)
--bitwuzla-dir=STR      custom Bitwuzla install prefix  (default: deps/bitwuzla)
--z3-dir=STR            custom Z3 install prefix        (default: deps/z3)

CMake Options (Advanced)
  -DVAR=VALUE              manually add CMake options
EOF
  exit 0
}

die() {
  echo "*** $0: $*" 1>&2
  exit 1
}

build_dir=build
install_prefix=default
build_btor=default
build_bitwuzla=default
build_cvc5=default
build_msat=default
build_yices2=default
build_z3=default
btor_dir=default
btor_src_dir=default
cvc5_dir=default
msat_dir=default
yices2_dir=default
static=default
auto_deps=default
allow_gpl=default
build_tests=default
system_gtest=default
python=default
python_executable=default
smtlib_reader=default
bison_dir=default
flex_dir=default
bitwuzla_dir=default
z3_dir=default

# Rotate once through the arguments. Each flag is consumed here; anything that
# has to reach CMake is pushed back onto "$@", so that after the loop "$@"
# holds exactly the CMake options, each one still a single word.
argc=$#
i=0
while [ "$i" -lt "$argc" ]; do
  arg=$1
  shift
  i=$((i + 1))
  case $arg in
    -h | --help) usage ;;
    --prefix) die "missing argument to $arg (see -h)" ;;
    --prefix=*)
      install_prefix=${arg##*=}
      # Check if install_prefix is an absolute path and if not, make it
      # absolute.
      case $install_prefix in
        /*) ;;                                      # absolute path
        *) install_prefix=$(pwd)/$install_prefix ;; # make absolute path
      esac
      ;;
    --btor)
      build_btor=ON
      ;;
    --bitwuzla)
      build_bitwuzla=ON
      ;;
    --yices2)
      build_yices2=ON
      ;;
    --cvc5)
      build_cvc5=ON
      ;;
    --msat)
      build_msat=ON
      ;;
    --z3)
      build_z3=ON
      ;;
    # The --*-home flags named a source tree with the build inside it. Their
    # replacements name an install prefix, so silently accepting the old
    # spelling would point CMake at the wrong directory.
    --btor-home | --btor-home=*)
      die "$arg was replaced by --btor-dir, which takes an install prefix;" \
        "the source tree is --btor-src-dir (see -h)"
      ;;
    --cvc5-home | --cvc5-home=*)
      die "$arg was replaced by --cvc5-dir," \
        "which takes an install prefix (see -h)"
      ;;
    --msat-home | --msat-home=*)
      die "$arg was replaced by --msat-dir," \
        "which takes an install prefix (see -h)"
      ;;
    --yices2-home | --yices2-home=*)
      die "$arg was replaced by --yices2-dir," \
        "which takes an install prefix (see -h)"
      ;;
    --z3-install-dir | --z3-install-dir=*)
      die "$arg was replaced by --z3-dir (see -h)"
      ;;
    --btor-dir) die "missing argument to $arg (see -h)" ;;
    --btor-dir=*)
      btor_dir=${arg##*=}
      # Check if btor_dir is an absolute path and if not, make it
      # absolute.
      case $btor_dir in
        /*) ;;                          # absolute path
        *) btor_dir=$(pwd)/$btor_dir ;; # make absolute path
      esac
      ;;
    --btor-src-dir) die "missing argument to $arg (see -h)" ;;
    --btor-src-dir=*)
      btor_src_dir=${arg##*=}
      # Check if btor_src_dir is an absolute path and if not, make it
      # absolute.
      case $btor_src_dir in
        /*) ;;                                  # absolute path
        *) btor_src_dir=$(pwd)/$btor_src_dir ;; # make absolute path
      esac
      ;;
    --cvc5-dir) die "missing argument to $arg (see -h)" ;;
    --cvc5-dir=*)
      cvc5_dir=${arg##*=}
      # Check if cvc5_dir is an absolute path and if not, make it
      # absolute.
      case $cvc5_dir in
        /*) ;;                          # absolute path
        *) cvc5_dir=$(pwd)/$cvc5_dir ;; # make absolute path
      esac
      ;;
    --msat-dir) die "missing argument to $arg (see -h)" ;;
    --msat-dir=*)
      msat_dir=${arg##*=}
      # Check if msat_dir is an absolute path and if not, make it
      # absolute.
      case $msat_dir in
        /*) ;;                          # absolute path
        *) msat_dir=$(pwd)/$msat_dir ;; # make absolute path
      esac
      ;;
    --yices2-dir) die "missing argument to $arg (see -h)" ;;
    --yices2-dir=*)
      yices2_dir=${arg##*=}
      # Check if yices2_dir is an absolute path and if not, make it
      # absolute.
      case $yices2_dir in
        /*) ;;                              # absolute path
        *) yices2_dir=$(pwd)/$yices2_dir ;; # make absolute path
      esac
      ;;
    --build-dir) die "missing argument to $arg (see -h)" ;;
    --build-dir=*)
      build_dir=${arg##*=}
      # Check if build_dir is an absolute path and if not, make it
      # absolute.
      case $build_dir in
        /*) ;;                            # absolute path
        *) build_dir=$(pwd)/$build_dir ;; # make absolute path
      esac
      ;;
    --debug)
      die "$arg was removed; pass -DCMAKE_BUILD_TYPE=Debug instead," \
        "or see DEVELOPERS.md for building Release and Debug side by side"
      ;;
    --static)
      static=yes
      ;;
    --no-auto-deps)
      auto_deps=no
      ;;
    --allow-gpl)
      allow_gpl=yes
      ;;
    --without-tests)
      build_tests=no
      ;;
    --no-system-gtest)
      system_gtest=no
      ;;
    --python)
      python=yes
      ;;
    --python-executable=*)
      python_executable=${arg##*=}
      # Check if python_executable is an absolute path and if not, make it
      # absolute.
      case $python_executable in
        /*) ;;                                            # absolute path
        *) python_executable=$(pwd)/$python_executable ;; # make absolute path
      esac
      ;;
    --smtlib-reader)
      smtlib_reader=yes
      ;;
    --bison-dir=*)
      bison_dir=${arg##*=}
      # Check if bison_dir is an absolute path and if not, make it
      # absolute.
      case $bison_dir in
        /*) ;;                            # absolute path
        *) bison_dir=$(pwd)/$bison_dir ;; # make absolute path
      esac
      ;;
    --flex-dir=*)
      flex_dir=${arg##*=}
      # Check if flex_dir is an absolute path and if not, make it
      # absolute.
      case $flex_dir in
        /*) ;;                          # absolute path
        *) flex_dir=$(pwd)/$flex_dir ;; # make absolute path
      esac
      ;;
    --bitwuzla-dir) die "missing argument to $arg (see -h)" ;;
    --bitwuzla-dir=*)
      bitwuzla_dir=${arg##*=}
      # Make relative paths absolute
      bitwuzla_dir=$(cd -- "$bitwuzla_dir" && pwd)
      ;;
    --z3-dir) die "missing argument to $arg (see -h)" ;;
    --z3-dir=*)
      z3_dir=${arg##*=}
      # Make relative paths absolute
      z3_dir=$(cd -- "$z3_dir" && pwd)
      ;;
    -D*) set -- "$@" "$arg" ;;
    *) die "unexpected argument: $arg" ;;
  esac
done

# enable solvers automatically if a custom directory is provided
if [ "$btor_dir" != default ] || [ "$btor_src_dir" != default ]; then
  if [ "$build_btor" = default ]; then
    build_btor=ON
  fi
fi

if [ "$bitwuzla_dir" != default ] && [ "$build_bitwuzla" = default ]; then
  build_bitwuzla=ON
fi

if [ "$cvc5_dir" != default ] && [ "$build_cvc5" = default ]; then
  build_cvc5=ON
fi

if [ "$msat_dir" != default ] && [ "$build_msat" = default ]; then
  build_msat=ON
fi

if [ "$yices2_dir" != default ] && [ "$build_yices2" = default ]; then
  build_yices2=ON
fi

if [ "$z3_dir" != default ] && [ "$build_z3" = default ]; then
  build_z3=ON
fi

# "$@" already holds any -D options given on the command line. Append the
# options derived from the flags above, so that an explicit -D comes first and
# the derived value wins if both set the same variable. The build type is the
# exception: no flag sets it, so the default goes first and an explicit
# -DCMAKE_BUILD_TYPE overrides it.
set -- "-DCMAKE_BUILD_TYPE=Release" "$@"

[ "$install_prefix" != default ] &&
  set -- "$@" "-DCMAKE_INSTALL_PREFIX=$install_prefix"

[ "$build_btor" != default ] &&
  set -- "$@" "-DBUILD_BTOR=$build_btor"

[ "$build_bitwuzla" != default ] &&
  set -- "$@" "-DBUILD_BITWUZLA=$build_bitwuzla"

[ "$build_cvc5" != default ] &&
  set -- "$@" "-DBUILD_CVC5=$build_cvc5"

[ "$build_msat" != default ] &&
  set -- "$@" "-DBUILD_MSAT=$build_msat"

[ "$build_yices2" != default ] &&
  set -- "$@" "-DBUILD_YICES2=$build_yices2"

[ "$build_z3" != default ] &&
  set -- "$@" "-DBUILD_Z3=$build_z3"

[ "$btor_dir" != default ] &&
  set -- "$@" "-DBoolector_ROOT=$btor_dir"

[ "$btor_src_dir" != default ] &&
  set -- "$@" "-DBoolector_SOURCE_DIR=$btor_src_dir"

[ "$cvc5_dir" != default ] &&
  set -- "$@" "-Dcvc5_ROOT=$cvc5_dir"

[ "$msat_dir" != default ] &&
  set -- "$@" "-DMathSAT_ROOT=$msat_dir"

[ "$yices2_dir" != default ] &&
  set -- "$@" "-DYices2_ROOT=$yices2_dir"

[ "$static" != default ] &&
  set -- "$@" "-DSMT_SWITCH_LIB_TYPE=STATIC"

[ "$build_tests" != default ] &&
  set -- "$@" "-DBUILD_TESTS=$build_tests"

[ "$system_gtest" != default ] &&
  set -- "$@" "-DSYSTEM_GTEST=$system_gtest"
[ "$auto_deps" != default ] &&
  set -- "$@" "-DSMT_SWITCH_AUTO_DEPS=OFF"
[ "$allow_gpl" != default ] &&
  set -- "$@" "-DSMT_SWITCH_ALLOW_GPL=ON"

[ "$python" != default ] &&
  set -- "$@" "-DBUILD_PYTHON_BINDINGS=ON"

[ "$python_executable" != default ] &&
  set -- "$@" "-DPython_EXECUTABLE=$python_executable"

[ "$smtlib_reader" != default ] &&
  set -- "$@" "-DSMTLIB_READER=ON"

[ "$bison_dir" != default ] &&
  set -- "$@" "-DBISON_ROOT=$bison_dir"

[ "$flex_dir" != default ] &&
  set -- "$@" "-DFLEX_ROOT=$flex_dir"

[ "$bitwuzla_dir" != default ] &&
  set -- "$@" "-DBitwuzla_ROOT=$bitwuzla_dir"

[ "$z3_dir" != default ] &&
  set -- "$@" "-DZ3_ROOT=$z3_dir"

mkdir -p "$build_dir"
cd "$build_dir" || exit 1

# Reset build configuration.
[ -e CMakeCache.txt ] && rm CMakeCache.txt

echo "Running with cmake options: $*"
cmake .. "$@" 2>&1
