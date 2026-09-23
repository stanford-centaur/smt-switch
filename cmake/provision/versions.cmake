# Pinned versions of the dependencies this project can build for itself.
#
# Bumping one here rebuilds that dependency and everything that depends on it:
# the URL is
# baked into the download script ExternalProject generates, and that script is
# a dependency of the download step.
#
# GitHub archive URLs take the commit for a pin that names one and the tag
# path for a pin that names a tag. Where both are known the commit is used,
# with the tag in a comment, so that the pin stays fixed even if a tag moves.
#
# Every pin carries the SHA-256 of what its URL serves, which is what decides
# whether we compile what we meant to. cmake/provision/CMakeLists.txt refuses
# to configure without one. Recompute them with
#
#   cmake -P cmake/provision/refresh-hashes.cmake <name>...
#
# Note that a GitHub /archive/ URL is generated on request rather than stored,
# and GitHub does not promise to generate the same bytes forever. A pin naming
# a commit fixes the contents but not the compression. If every GitHub pin
# fails verification at once, suspect that rather than seven bad downloads.

set(CADICAL_VERSION 2.1.3)
set(
  CADICAL_URL
  "https://github.com/arminbiere/cadical/archive/refs/tags/rel-${CADICAL_VERSION}.tar.gz"
)
set(CADICAL_SHA256 abfe890aa4ccda7b8449c7ad41acb113cfb8e7e8fbf5e49369075f9b00d70465)

# 2025-09-18
set(BTOR2TOOLS_COMMIT d33c73ff1d173f1bfac8ba6b1c6d68ba62c55f8e)
set(BTOR2TOOLS_URL "https://github.com/hwmcc/btor2tools/archive/${BTOR2TOOLS_COMMIT}.tar.gz")
set(BTOR2TOOLS_SHA256 55c0b62d42b2dbbb14ebb9e4c405d127df1a92f7bfd3f5276ab862c9f9369e26)

set(BOOLECTOR_VERSION 3.2.4)
set(
  BOOLECTOR_URL
  "https://github.com/boolector/boolector/archive/refs/tags/${BOOLECTOR_VERSION}.tar.gz"
)
set(BOOLECTOR_SHA256 249c6dbf4e52ea6e8df1ddf7965d47f5c30f2c14905dce9b8f411756b05878bf)

# 0.9.1
set(BITWUZLA_COMMIT 8d1eb01093ae54d9b4586456b69c3bf31000a4c2)
set(BITWUZLA_URL "https://github.com/bitwuzla/bitwuzla/archive/${BITWUZLA_COMMIT}.tar.gz")
set(BITWUZLA_SHA256 326ba90cb20aa8c4ebb56ab4e353362993aad4af585a05ea31139ebc9a30e4fc)

# cvc5-1.4.0
set(CVC5_COMMIT b432cd77ebeb41091de42637ca8523f8437a1db1)
set(CVC5_URL "https://github.com/cvc5/cvc5/archive/${CVC5_COMMIT}.tar.gz")
set(CVC5_SHA256 6c5a9044021b7cedf6cb11348abc4828c97a65fe338dec308a432d6cf982c37f)

# z3-5.1.0
set(Z3_COMMIT 0b6cdcdbc65da25ef0f73ac9da210574d0f66cf8)
set(Z3_URL "https://github.com/Z3Prover/z3/archive/${Z3_COMMIT}.tar.gz")
set(Z3_SHA256 321daec4cc662dab152abc76ada056db38735dca9fe1c9b340c029357e71837f)

# yices-2.7.0
set(YICES2_COMMIT 85cf17e44eac76b5d14b297c09fc9bfecf47ef65)
set(YICES2_URL "https://github.com/SRI-CSL/yices2/archive/${YICES2_COMMIT}.tar.gz")
set(YICES2_SHA256 37ba930fddde2b087e5a95097a9cec5010510346aad8a0987204e6decd220898)

# Not a solver. Provisioned only where the system bison is older than the
# 3.7.0 the SMT-LIB reader needs, which on macOS is the default. The one pin
# that names a release tarball rather than a generated archive.
set(BISON_VERSION 3.8.2)
set(BISON_URL "https://mirror.us-midwest-1.nexcess.net/gnu/bison/bison-${BISON_VERSION}.tar.gz")
set(BISON_SHA256 06c9e13bdf7eb24d4ceb6b59205a4f67c2c7e7213119644430fe82fbd14a0abb)
