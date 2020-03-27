#!/bin/bash

if [ $# -lt 2 ]; then
   echo "usage: $0 <libname> [...libs to combine]"
   exit 1
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

