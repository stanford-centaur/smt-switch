#!/bin/bash

if [ "$TRAVIS_OS_NAME" == "osx" ]; then
    ruby -e "$(curl -fsSL https://raw.githubusercontent.com/Homebrew/install/master/install)"
    export PATH=/usr/local/bin:/usr/local/sbin:$PATH
    brew install python
else
    echo "NOT in OSX -- nothing to do"
fi
