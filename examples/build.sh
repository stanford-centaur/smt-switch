# get the absolute path to this directory
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"

# go to main repo directory
cd $DIR/..

# pull and build the dependencies
# if they're already built, it will just fail and that's fine
./contrib/setup-btor.sh
./contrib/setup-cvc4.sh

# configure and build smt-switch with boolector and cvc4 backends
# set it up to be installed in a directory called example-install in the examples directory
# also use a build directory in the examples directory
./configure.sh --btor --cvc4 --prefix=./examples/example-install --build-dir=$DIR/example-build
cd $DIR/example-build
make -j
make test
make -j install

cd $DIR
# now make the examples
make
