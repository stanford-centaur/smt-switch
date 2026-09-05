#!/bin/bash
version=2.6.4
release_base=https://github.com/westes/flex/releases/download
source_url=$release_base/v$version/flex-$version.tar.gz

# shellcheck source=contrib/make-setup.sh
source "$(dirname "$0")/make-setup.sh"
