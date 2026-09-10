#!/bin/bash
version=3.8.2
_mirror_host=mirror.us-midwest-1.nexcess.net
source_url=https://$_mirror_host/gnu/bison/bison-$version.tar.gz

# shellcheck source=contrib/make-setup.sh
source "$(dirname "$0")/make-setup.sh"
