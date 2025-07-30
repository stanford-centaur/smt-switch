#!/bin/sh

# Syntax and structure borrowed from CVC5's configure.sh script

CONF_FILE=Makefile.conf

usage () {
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
--btor-home=STR         custom BTOR location    (default: deps/boolector)
--cvc5-home=STR         custom cvc5 location    (default: deps/cvc5)
--msat-home=STR         custom MathSAT location (default: deps/mathsat)
--yices2-home=STR       custom YICES2 location  (default: deps/yices2)
--build-dir=STR         custom build directory  (default: build)
--debug                 build debug with debug symbols (default: off)
--static                create static libaries (default: off)
--without-tests         build without the smt-switch test suite (default: off)
--no-system-gtest       do not use system GTest sources; forces download (default: off)
--python                compile with python bindings (default: off)
--python-executabe      point to a particular Python interpreter - will look around this for include and lib dirs
--smtlib-reader         include the smt-lib reader - requires bison/flex (default:off)
--bison-dir=STR         custom bison installation directory
--flex-dir=STR          custom flex installation directory
--bitwuzla-dir=STR      custom Bitwuzla installation directory
--z3-install-dir=STR    custom Z3 installation directory (default: deps/install)

CMake Options (Advanced)
  -DVAR=VALUE              manually add CMake options
EOF
  exit 0
}

die () {
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
btor_home=default
cvc5_home=default
msat_home=default
yices2_home=default
static=default
build_tests=default
system_gtest=default
python=default
python_executable=default
smtlib_reader=default
bison_dir=default
flex_dir=default
bitwuzla_dir=default
z3_install_dir=default

build_type=Release

cmake_opts=""

while [ $# -gt 0 ]
do
    case $1 in
        -h|--help) usage;;
        --prefix) die "missing argument to $1 (see -h)" ;;
        --prefix=*)
            install_prefix=${1##*=}
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
            --btor-home) die "missing argument to $1 (see -h)" ;;
            --btor-home=*)
                btor_home=${1##*=}
                # Check if btor_home is an absolute path and if not, make it
                # absolute.
                case $btor_home in
                    /*) ;;                                      # absolute path
                    *) btor_home=$(pwd)/$btor_home ;; # make absolute path
                esac
                ;;
        --cvc5-home) die "missing argument to $1 (see -h)" ;;
        --cvc5-home=*)
            cvc5_home=${1##*=}
            # Check if cvc5_home is an absolute path and if not, make it
            # absolute.
            case $cvc5_home in
                /*) ;;                                      # absolute path
                *) cvc5_home=$(pwd)/$cvc5_home ;; # make absolute path
            esac
            ;;
        --msat-home) die "missing argument to $1 (see -h)" ;;
        --msat-home=*)
            msat_home=${1##*=}
            # Check if msat_home is an absolute path and if not, make it
            # absolute.
            case $msat_home in
                /*) ;;                                      # absolute path
                *) msat_home=$(pwd)/$msat_home ;; # make absolute path
            esac
            ;;
        --yices2-home) die "missing argument to $1 (see -h)" ;;
        --yices2-home=*)
            yices2_home=${1##*=}
            # Check if yices2_home is an absolute path and if not, make it
            # absolute.
            case $yices2_home in
                /*) ;;                                      # absolute path
                *) yices2_home=$(pwd)/$yices2_home ;; # make absolute path
            esac
            ;;
        --build-dir) die "missing argument to $1 (see -h)" ;;
        --build-dir=*)
            build_dir=${1##*=}
            # Check if build_dir is an absolute path and if not, make it
            # absolute.
            case $build_dir in
                /*) ;;                                      # absolute path
                *) build_dir=$(pwd)/$build_dir ;; # make absolute path
            esac
            ;;
        --debug)
            build_type=Debug;
            ;;
        --static)
            static=yes
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
            python_executable=${1##*=}
            # Check if python_executable is an absolute path and if not, make it
            # absolute.
            case $python_executable in
                /*) ;;                            # absolute path
                *) python_executable=$(pwd)/$python_executable ;; # make absolute path
            esac
            ;;
        --smtlib-reader)
            smtlib_reader=yes
            ;;
        --bison-dir=*)
            bison_dir=${1##*=}
            # Check if bison_dir is an absolute path and if not, make it
            # absolute.
            case $bison_dir in
                /*) ;;                            # absolute path
                *) bison_dir=$(pwd)/$bison_dir ;; # make absolute path
            esac
            ;;
        --flex-dir=*)
            flex_dir=${1##*=}
            # Check if flex_dir is an absolute path and if not, make it
            # absolute.
            case $flex_dir in
                /*) ;;                            # absolute path
                *) flex_dir=$(pwd)/$flex_dir ;; # make absolute path
            esac
            ;;
        --bitwuzla-dir) die "missing argument to $1 (see -h)" ;;
        --bitwuzla-dir=*)
            bitwuzla_dir="${1##*=}"
            # Make relative paths absolute
            bitwuzla_dir="$(cd -- "$bitwuzla_dir" && pwd)"
            ;;
        --z3-install-dir) die "missing argument to $1 (see -h)" ;;
        --z3-install-dir=*)
            z3_install_dir=${1##*=}
            # Make relative paths absolute
            z3_install_dir="$(cd -- "$z3_install_dir" && pwd)"
            ;;
        -D*) cmake_opts="${cmake_opts} $1" ;;
        *) die "unexpected argument: $1";;
    esac
    shift
done

# enable solvers automatically if a custom home is provided
if [ $btor_home != default -a $build_btor = default ]; then
    build_btor=ON
fi

if [ $cvc5_home != default -a $build_cvc5 = default ]; then
    build_cvc5=ON
fi

if [ $msat_home != default -a $build_msat = default ]; then
    build_msat=ON
fi

if [ $yices2_home != default -a $build_yices2 = default ]; then
    build_yices2=ON
fi

cmake_opts="$cmake_opts -DCMAKE_BUILD_TYPE=$build_type"

[ $install_prefix != default ] \
    && cmake_opts="$cmake_opts -DCMAKE_INSTALL_PREFIX=$install_prefix"

[ $build_btor != default ] \
    && cmake_opts="$cmake_opts -DBUILD_BTOR=$build_btor"

[ $build_bitwuzla != default ] \
    && cmake_opts="$cmake_opts -DBUILD_BITWUZLA=$build_bitwuzla"

[ $build_cvc5 != default ] \
    && cmake_opts="$cmake_opts -DBUILD_CVC5=$build_cvc5"

[ $build_msat != default ] \
    && cmake_opts="$cmake_opts -DBUILD_MSAT=$build_msat"

[ $build_yices2 != default ] \
    && cmake_opts="$cmake_opts -DBUILD_YICES2=$build_yices2"

[ $build_z3 != default ] \
    && cmake_opts="$cmake_opts -DBUILD_Z3=$build_z3"

[ $btor_home != default ] \
    && cmake_opts="$cmake_opts -DBTOR_HOME=$btor_home"

[ $cvc5_home != default ] \
    && cmake_opts="$cmake_opts -DCVC5_HOME=$cvc5_home"

[ $msat_home != default ] \
    && cmake_opts="$cmake_opts -DMSAT_HOME=$msat_home"

[ $yices2_home != default ] \
    && cmake_opts="$cmake_opts -DYICES2_HOME=$yices2_home"

[ $static != default ] \
    && cmake_opts="$cmake_opts -DSMT_SWITCH_LIB_TYPE=STATIC"

[ $build_tests != default ] \
    && cmake_opts="$cmake_opts -DBUILD_TESTS=$build_tests"

[ $system_gtest != default ] \
    && cmake_opts="$cmake_opts -DSYSTEM_GTEST=$system_gtest"

[ $python != default ] \
    && cmake_opts="$cmake_opts -DBUILD_PYTHON_BINDINGS=ON"

[ $python_executable != default ] \
    && cmake_opts="$cmake_opts -DPython_EXECUTABLE=$python_executable"

[ $smtlib_reader != default ] \
    && cmake_opts="$cmake_opts -DSMTLIB_READER=ON"

[ $bison_dir != default ] \
    && cmake_opts="$cmake_opts -DBISON_DIR=$bison_dir"

[ $flex_dir != default ] \
    && cmake_opts="$cmake_opts -DFLEX_DIR=$flex_dir"

[ $bitwuzla_dir != default ] \
    && cmake_opts="$cmake_opts -DBITWUZLA_DIR=$bitwuzla_dir"

[ $z3_install_dir != default ] \
    && cmake_opts="$cmake_opts -DZ3_INSTALL_DIR=$z3_install_dir"

mkdir -p "$build_dir"
cd "$build_dir" || exit 1

# Reset build configuration.
[ -e CMakeCache.txt ] && rm CMakeCache.txt

echo "Running with cmake options: $cmake_opts"
cmake .. $cmake_opts 2>&1
