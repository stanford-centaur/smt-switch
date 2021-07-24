#!/bin/sh

# Syntax and structure borrowed from CVC4's configure.sh script

CONF_FILE=Makefile.conf

usage () {
cat <<EOF
Usage: $0 [<option> ...]

Configures the CMAKE build environment.

-h, --help              display this message and exit
--prefix=STR            install directory       (default: /usr/local/)
--btor                  build boolector         (default: off)
--bitwuzla              build bitwuzla            (default: off)
--cvc4                  build cvc4              (default: off)
--msat                  build MathSAT           (default: off)
--yices2                build yices2            (default: off)
--z3                    build z3                (default: off)
--ipasir                build ipasir               (default: off)
--btor-home=STR         custom BTOR location    (default: deps/boolector)
--bitwuzla-home=STR     custom Bitwuzla location  (default: deps/bitwuzla)
--cvc4-home=STR         custom CVC4 location    (default: deps/CVC4)
--msat-home=STR         custom MathSAT location (default: deps/mathsat)
--yices2-home=STR       custom YICES2 location  (default: deps/yices2)
--z3-home=STR           custom Z3 location      (default: deps/z3)
--ipasir-home=STR       custom IPASIR location      (default: deps/ipasir)
--build-dir=STR         custom build directory  (default: build)
--debug                 build debug with debug symbols (default: off)
--static                create static libaries (default: off)
--python                compile with python bindings (default: off)
--smtlib-reader         include the smt-lib reader - requires bison/flex (default:off)
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
build_cvc4=default
build_msat=default
build_yices2=default
build_z3=default
build_ipasir=default
btor_home=default
bitwuzla_home=default
cvc4_home=default
msat_home=default
yices2_home=default
z3_home=default
ipasir_home=default
static=default
python=default
smtlib_reader=default

build_type=Release

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
        --cvc4)
            build_cvc4=ON
            ;;
        --msat)
            build_msat=ON
            ;;
		--z3)
	   		build_z3=ON
	    	;;
        --ipasir)
            build_ipasir=ON
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
        --bitwuzla-home) die "missing argument to $1 (see -h)" ;;
        --bitwuzla-home=*)
            bitwuzla_home=${1##*=}
            # Check if bitwuzla_home is an absolute path and if not, make it
            # absolute.
            case $bitwuzla_home in
                /*) ;;                                      # absolute path
                *) bitwuzla_home=$(pwd)/$bitwuzla_home ;; # make absolute path
            esac
            ;;
        --cvc4-home) die "missing argument to $1 (see -h)" ;;
        --cvc4-home=*)
            cvc4_home=${1##*=}
            # Check if cvc4_home is an absolute path and if not, make it
            # absolute.
            case $cvc4_home in
                /*) ;;                                      # absolute path
                *) cvc4_home=$(pwd)/$cvc4_home ;; # make absolute path
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
		--z3-home) die "missing argument to $1 (see -h)" ;;
        --z3-home=*)
            z3_home=${1##*=}
            # Check if z3_home is an absolute path and if not, make it
            # absolute.
            case $z3_home in
                /*) ;;                                      # absolute path
                *) z3_home=$(pwd)/$z3_home ;; # make absolute path
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
        --ipasir-home) die "missing argument to $1 (see -h)" ;;
        --ipasir-home=*)
            ipasir_home=${1##*=}
            # Check if ipasir_home is an absolute path and if not, make it
            # absolute.
            case $ipasir_home in
                /*) ;;                                      # absolute path
                *) ipasir_home=$(pwd)/$ipasir_home ;; # make absolute path
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
        --python)
            python=yes
            ;;
        --smtlib-reader)
            smtlib_reader=yes
            ;;
        *) die "unexpected argument: $1";;
    esac
    shift
done

# enable solvers automatically if a custom home is provided
if [ $btor_home != default -a $build_btor = default ]; then
    build_btor=ON
fi

if [ $bitwuzla_home != default -a $build_bitwuzla = default ]; then
    build_bitwuzla=ON
fi

if [ $cvc4_home != default -a $build_cvc4 = default ]; then
    build_cvc4=ON
fi

if [ $msat_home != default -a $build_msat = default ]; then
    build_msat=ON
fi

if [ $yices2_home != default -a $build_yices2 = default ]; then
    build_yices2=ON
fi

if [ $ipasir_home != default -a $build_ipasir = default ]; then
    build_ipasir=ON
fi

cmake_opts="-DCMAKE_BUILD_TYPE=$build_type"

[ $install_prefix != default ] \
    && cmake_opts="$cmake_opts -DCMAKE_INSTALL_PREFIX=$install_prefix"

[ $build_btor != default ] \
    && cmake_opts="$cmake_opts -DBUILD_BTOR=$build_btor"

[ $build_bitwuzla != default ] \
    && cmake_opts="$cmake_opts -DBUILD_BITWUZLA=$build_bitwuzla"

[ $build_cvc4 != default ] \
    && cmake_opts="$cmake_opts -DBUILD_CVC4=$build_cvc4"

[ $build_msat != default ] \
    && cmake_opts="$cmake_opts -DBUILD_MSAT=$build_msat"

[ $build_z3 != default ] \
    && cmake_opts="$cmake_opts -DBUILD_Z3=$build_z3"

[ $build_yices2 != default ] \
    && cmake_opts="$cmake_opts -DBUILD_YICES2=$build_yices2"

[ $build_ipasir != default ] \
    && cmake_opts="$cmake_opts -DBUILD_IPASIR=$build_ipasir"

[ $btor_home != default ] \
    && cmake_opts="$cmake_opts -DBTOR_HOME=$btor_home"

[ $bitwuzla_home != default ] \
    && cmake_opts="$cmake_opts -DBITWUZLA_HOME=$bitwuzla_home"

[ $cvc4_home != default ] \
    && cmake_opts="$cmake_opts -DCVC4_HOME=$cvc4_home"

[ $msat_home != default ] \
    && cmake_opts="$cmake_opts -DMSAT_HOME=$msat_home"

[ $z3_home != default ] \
    && cmake_opts="$cmake_opts -DZ3_HOME=$z3_home"

[ $yices2_home != default ] \
    && cmake_opts="$cmake_opts -DYICES2_HOME=$yices2_home"

[ $ipasir_home != default ] \
    && cmake_opts="$cmake_opts -DIPASIR_HOME=$ipasir_home"

[ $static != default ] \
    && cmake_opts="$cmake_opts -DSMT_SWITCH_LIB_TYPE=STATIC"

[ $python != default ] \
    && cmake_opts="$cmake_opts -DBUILD_PYTHON_BINDINGS=ON"

[ $smtlib_reader != default ] \
    && cmake_opts="$cmake_opts -DSMTLIB_READER=ON"

root_dir=$(pwd)

[ -e "$build_dir" ] && rm -r "$build_dir"

mkdir -p "$build_dir"
cd "$build_dir" || exit 1

[ -e CMakeCache.txt ] && rm CMakeCache.txt

echo "Running with cmake options: $cmake_opts"

cmake "$root_dir" $cmake_opts 2>&1
