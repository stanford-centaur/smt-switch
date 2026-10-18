# The environment that the CI scripts and workflow steps share.
# shellcheck shell=bash

# The system packages that are not on the runner images so need to be installed.
# MacOS has bison already, but its version is too old for the SMT-LIB reader.
export APT_PACKAGES="gperf libgmp-dev libmpfr-dev"
export BREW_PACKAGES="autoconf bison"

# This keeps brew install from updating Homebrew first.
export HOMEBREW_NO_AUTO_UPDATE=1

# We use this GNU mirror instead of the default one, because it is more
# reliable and provides high bandwidth.
export GNU_MIRROR="https://mirror.us-midwest-1.nexcess.net/gnu"
