# The environment that the CI scripts and workflow steps share.
# shellcheck shell=bash

# The system packages that are not on the runner images so need to be installed.
# MacOS has bison already, but its version is too old for the SMT-LIB reader.
# LibPoly and CUDD give Yices2 MCSAT, which it needs for nonlinear arithmetic.
# CUDD comes from SRI-CSL's PPA and tap; LibPoly is built by install-libpoly.sh.
export APT_PACKAGES="gperf libgmp-dev libmpfr-dev cudd dh-exec fakeroot"
export BREW_PACKAGES="autoconf bison SRI-CSL/sri-csl/cudd"

# This keeps brew install from updating Homebrew first.
export HOMEBREW_NO_AUTO_UPDATE=1

# We use this GNU mirror instead of the default one, because it is more
# reliable and provides high bandwidth.
export GNU_MIRROR="https://mirror.us-midwest-1.nexcess.net/gnu"
