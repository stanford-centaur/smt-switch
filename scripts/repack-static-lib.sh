#!/bin/bash

if [ $# -lt 2 ]; then
  echo "usage: $0 <libname> [...libs to combine]"
  exit 1
fi

if [[ $OSTYPE == linux* || $OSTYPE == cygwin* ]]; then
  # use a GNU ar MRI script on Linux-like systems
  if ! command -v ar &>/dev/null; then
    echo "ar could not be found"
    echo "required for repacking static libraries on Linux"
    exit
  fi

  target=$1
  mri_command="create $target"
  for lib in "${@:2}"; do
    mri_command="${mri_command}\naddlib $lib"
  done

  mri_command="${mri_command}\nsave\nend"
  echo -e "$mri_command" | ar -M

  if [ ! -f "${target}" ]; then
    echo "It appears ar failed to create ${target}"
    exit 1
  fi
elif [[ $OSTYPE == darwin* ]]; then
  # use libtool (note: not the same as GNU libtool) on OSX
  if ! command -v libtool &>/dev/null; then
    echo "libtool could not be found"
    echo "required for repacking static libraries on Mac"
    exit
  fi

  libtool -static -o "$@"
elif [[ $OSTYPE == msys* ]]; then
  echo "$0 does not support repacking static libs on Windows yet"
else
  echo "Unrecognized OSTYPE=$OSTYPE"
  exit 1
fi
