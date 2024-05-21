#!/bin/bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps
VERSION=3.8.2

mkdir -p $DEPS

if [ -d "$DEPS/bison" ]; then
    echo "It appears bison has already been downloaded to $DEPS/bison"
    echo "If you'd like to rebuild, please delete it and run this script again"
    exit 1
fi

curl http://ftp.gnu.org/gnu/bison/bison-$VERSION.tar.xz --output $DEPS/bison-$VERSION.tar.xz

if [ ! -f "$DEPS/bison-$VERSION.tar.xz" ]; then
    echo "It seems like downloading bison to $DEPS/bison-$VERSION.tar.xz failed"
    exit 1
fi

cd $DEPS
tar -xf bison-$VERSION.tar.xz
rm bison-$VERSION.tar.xz
mv ./bison-$VERSION ./bison
cd bison
mkdir bison-install
./configure --prefix $DEPS/bison/bison-install --exec-prefix $DEPS/bison/bison-install
make -j$(nproc)
make install
cd $DIR

if [ ! -f "$DEPS/bison/bison-install/bin/bison" ]; then
    echo "It seems like installing bison to $DEPS/bison/bison-install failed"
    exit 1
fi
