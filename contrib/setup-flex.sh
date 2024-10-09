#!/bin/bash
set -e

DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ -d "$DEPS/flex" ]; then
    echo "It appears flex has already been downloaded to $DEPS/flex"
    echo "If you'd like to rebuild, please delete it and run this script again"
    exit 1
fi

curl -Lk https://github.com/westes/flex/releases/download/v2.6.4/flex-2.6.4.tar.gz --output $DEPS/flex-2.6.4.tar.gz

if [ ! -f "$DEPS/flex-2.6.4.tar.gz" ]; then
    echo "It seems like downloading flex to $DEPS/flex-2.6.4.tar.gz failed"
    exit 1
fi

if [ "$(uname)" == "Darwin" ]; then
    NUM_CORES=$(sysctl -n hw.logicalcpu)
elif [ "$(expr substr $(uname -s) 1 5)" == "Linux" ]; then
    NUM_CORES=$(nproc)
else
    NUM_CORES=1
fi

# Set CFLAGS to work around compiler issue with building flex
export CFLAGS="$CFLAGS -D_GNU_SOURCE"
cd $DEPS
tar -xf flex-2.6.4.tar.gz
rm flex-2.6.4.tar.gz
mv flex-2.6.4 flex
cd flex
mkdir flex-install
./configure --prefix $DEPS/flex/flex-install --exec-prefix $DEPS/flex/flex-install
make -j$NUM_CORES
make install
cd $DIR

if [ ! -f "$DEPS/flex/flex-install/bin/flex" ]; then
    echo "It seems like installing flex to $DEPS/flex/flex-install failed"
    exit 1
fi
