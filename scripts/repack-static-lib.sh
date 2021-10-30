#!/bin/bash

if [ $# -lt 2 ]; then
    echo "usage: $0 <libname> [...libs to combine]"
    exit 1
fi

if [[ "$OSTYPE" == linux* || "$OSTYPE" == cygwin* ]]; then
    # use a GNU ar MRI script on Linux-like systems
    if ! command -v ar &> /dev/null
    then
        echo "ar could not be found"
        echo "required for repacking static libraries on Linux"
        exit
    fi

    TARGET=$1
    MRI_COMMAND="create $TARGET"
    for lib in "${@:2}"; do
        MRI_COMMAND="${MRI_COMMAND}\naddlib $lib"
    done

    MRI_COMMAND="${MRI_COMMAND}\nsave\nend"
    echo -e "$MRI_COMMAND" | ar -M

    if [ ! -f "${TARGET}" ]; then
        echo "It appears ar failed to create ${TARGET}"
        exit 1
    fi
elif [[ "$OSTYPE" == darwin* ]]; then
    # use libtool (note: not the same as GNU libtool) on OSX
    if ! command -v libtool &> /dev/null
    then
        echo "libtool could not be found"
        echo "required for repacking static libraries on Mac"
        exit
    fi

    libtool -static -o $@
elif [[ "$OSTYPE" == msys* ]]; then
    echo "$0 does not support repacking static libs on Windows yet"
else
    echo "Unrecognized OSTYPE=$OSTYPE"
    exit 1
fi

