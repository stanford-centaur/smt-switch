# Pinned versions of the dependencies this project can build for itself.
#
# These were the pins in the contrib/setup-*.sh script headers. Bumping one
# here rebuilds that dependency and everything that depends on it: the URL is
# baked into the download script ExternalProject generates, and that script is
# a dependency of the download step.
#
# GitHub archive URLs take the commit for a pin that names one and the tag
# path for a pin that names a tag. Where both are known the commit is used,
# with the tag in a comment, so that the pin stays fixed even if a tag moves.

set(CADICAL_VERSION 2.1.3)
set(
  CADICAL_URL
  "https://github.com/arminbiere/cadical/archive/refs/tags/rel-${CADICAL_VERSION}.tar.gz"
)

# 2025-09-18
set(BTOR2TOOLS_COMMIT d33c73ff1d173f1bfac8ba6b1c6d68ba62c55f8e)
set(BTOR2TOOLS_URL "https://github.com/hwmcc/btor2tools/archive/${BTOR2TOOLS_COMMIT}.tar.gz")

set(BOOLECTOR_VERSION 3.2.4)
set(
  BOOLECTOR_URL
  "https://github.com/boolector/boolector/archive/refs/tags/${BOOLECTOR_VERSION}.tar.gz"
)

# 0.9.1
set(BITWUZLA_COMMIT 8d1eb01093ae54d9b4586456b69c3bf31000a4c2)
set(BITWUZLA_URL "https://github.com/bitwuzla/bitwuzla/archive/${BITWUZLA_COMMIT}.tar.gz")

# cvc5-1.4.0
set(CVC5_COMMIT b432cd77ebeb41091de42637ca8523f8437a1db1)
set(CVC5_URL "https://github.com/cvc5/cvc5/archive/${CVC5_COMMIT}.tar.gz")

# z3-5.1.0
set(Z3_COMMIT 0b6cdcdbc65da25ef0f73ac9da210574d0f66cf8)
set(Z3_URL "https://github.com/Z3Prover/z3/archive/${Z3_COMMIT}.tar.gz")

# yices-2.7.0
set(YICES2_COMMIT 85cf17e44eac76b5d14b297c09fc9bfecf47ef65)
set(YICES2_URL "https://github.com/SRI-CSL/yices2/archive/${YICES2_COMMIT}.tar.gz")

# Not a solver. Provisioned only where the system bison is older than the
# 3.7.0 the SMT-LIB reader needs, which on macOS is the default.
set(BISON_VERSION 3.8.2)
set(BISON_URL "https://mirror.us-midwest-1.nexcess.net/gnu/bison/bison-${BISON_VERSION}.tar.gz")
