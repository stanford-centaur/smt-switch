# The environment that the CI scripts and workflow steps share.
# shellcheck shell=bash

# The system packages that are not on the runner images so need to be installed.
# MacOS has bison already, but its version is too old for the SMT-LIB reader.
# Libraries that have to be built, such as LibPoly, are installed separately,
# by the install-extra-libraries scripts.
export APT_PACKAGES="gperf libgmp-dev libmpfr-dev"
export BREW_PACKAGES="autoconf bison"

# Where the install-extra-libraries scripts keep what they build, which CI
# caches.
export EXTRA_LIBRARIES_DIR=${RUNNER_TEMP:?}/extra-libraries

# The LibPoly release the install-extra-libraries scripts build, the one
# cvc5 requires, and the option they turn on in its packaging to build the
# position-independent archives a static cvc5 links.
export LIBPOLY_TAG=v0.2.1
export LIBPOLY_PIC_OPTION=-DLIBPOLY_BUILD_STATIC_PIC

# This keeps brew install from updating Homebrew first.
export HOMEBREW_NO_AUTO_UPDATE=1

# We use this GNU mirror instead of the default one, because it is more
# reliable and provides high bandwidth.
export GNU_MIRROR="https://mirror.us-midwest-1.nexcess.net/gnu"
