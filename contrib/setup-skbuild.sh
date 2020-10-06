#!/bin/bash

SKBUILD_VERSION=732f4c3f2a7e08c9154df4e5f7ddb9cd01d5044a
DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" >/dev/null 2>&1 && pwd )"
DEPS=$DIR/../deps

mkdir -p $DEPS

if [ ! -d "$DEPS/scikit-build" ]; then
    cd $DEPS
    git clone https://github.com/scikit-build/scikit-build.git
    cd scikit-build
    git checkout -f $SKBUILD_VERSION
    cd $DIR/../
else
    echo "$DEPS/scikit-build already exists. If you want to pull again, please remove it manually."
fi
