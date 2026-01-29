#!/bin/bash
version=2.6.4
source_url=https://github.com/westes/flex/releases/download/v$version/flex-$version.tar.gz

# shellcheck source=contrib/make-setup.sh
source "$(dirname "$0")/make-setup.sh"
