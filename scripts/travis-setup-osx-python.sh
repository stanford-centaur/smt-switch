#!/bin/bash

if [ "$TRAVIS_OS_NAME" == "osx" ]; then
    echo "In OSX"
else
    echo "NOT in OSX"
fi

