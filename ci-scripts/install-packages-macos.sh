#!/usr/bin/env bash
set -euo pipefail

# Install without first updating Homebrew. macOS's own gperf is new
# enough for yices2, unlike its bison for the SMT-LIB reader.
export HOMEBREW_NO_AUTO_UPDATE=1

brew install autoconf bison
