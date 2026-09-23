# Pinned versions of the dependencies this project can build for itself.
#
# Bumping one here rebuilds that dependency and everything that depends on
# it: the URL is baked into the download script ExternalProject generates,
# and that script is a dependency of the download step.
#
# GitHub archive URLs name the tag, which says what the pin is without having
# to look it up. A tag can be moved, but it cannot be moved past the hash
# below: the archive would change and the download would fail. btor2tools is
# the exception, naming a commit because the repository has no tags at all.
#
# Every pin carries the SHA-256 of what its URL serves, which is what decides
# whether we compile what we meant to. cmake/provision/CMakeLists.txt refuses
# to configure without one. Recompute them with
#
#   cmake -P cmake/provision/refresh-hashes.cmake <name>...
#
# Note that a GitHub /archive/ URL is generated on request rather than
# stored. GitHub guarantees the bytes only for assets a project uploads
# itself, which none of these publish, and has promised six months' notice
# before changing the archive format again. So if every GitHub pin fails
# verification at once, suspect that rather than seven bad downloads.

set(CADICAL_VERSION 2.1.3)
set(
  CADICAL_URL
  "https://github.com/arminbiere/cadical/archive/refs/tags/rel-${CADICAL_VERSION}.tar.gz"
)
set(CADICAL_SHA256 abfe890aa4ccda7b8449c7ad41acb113cfb8e7e8fbf5e49369075f9b00d70465)

set(BTOR2TOOLS_COMMIT d33c73ff1d173f1bfac8ba6b1c6d68ba62c55f8e)
set(BTOR2TOOLS_URL "https://github.com/hwmcc/btor2tools/archive/${BTOR2TOOLS_COMMIT}.tar.gz")
set(BTOR2TOOLS_SHA256 55c0b62d42b2dbbb14ebb9e4c405d127df1a92f7bfd3f5276ab862c9f9369e26)

set(BOOLECTOR_VERSION 3.2.4)
set(
  BOOLECTOR_URL
  "https://github.com/boolector/boolector/archive/refs/tags/${BOOLECTOR_VERSION}.tar.gz"
)
set(BOOLECTOR_SHA256 249c6dbf4e52ea6e8df1ddf7965d47f5c30f2c14905dce9b8f411756b05878bf)

set(BITWUZLA_VERSION 0.9.1)
set(
  BITWUZLA_URL
  "https://github.com/bitwuzla/bitwuzla/archive/refs/tags/${BITWUZLA_VERSION}.tar.gz"
)
set(BITWUZLA_SHA256 42707f38900a20bb18108e426ba667560d1fd2ccce0d4f75aa60439b546488b4)

set(CVC5_VERSION 1.4.0)
set(CVC5_URL "https://github.com/cvc5/cvc5/archive/refs/tags/cvc5-${CVC5_VERSION}.tar.gz")
set(CVC5_SHA256 06c65b30693d1abf7c1393b497c799950de2833457920b9433da8e418bce9113)

set(Z3_VERSION 5.1.0)
set(Z3_URL "https://github.com/Z3Prover/z3/archive/refs/tags/z3-${Z3_VERSION}.tar.gz")
set(Z3_SHA256 c433e1add0431c5edf1644bd9951c40588024d2d288f0e4215e5fcb6e3b4277d)

set(YICES2_VERSION 2.7.0)
set(
  YICES2_URL
  "https://github.com/SRI-CSL/yices2/archive/refs/tags/yices-${YICES2_VERSION}.tar.gz"
)
set(YICES2_SHA256 584db72abf6643927b2c3ba98ff793f602216b452b8ff2f34a8851d35904804a)

# Not a solver. Provisioned only where the system bison is older than the
# 3.7.0 the SMT-LIB reader needs, which on macOS is the default. The one pin
# that names a release tarball rather than a generated archive.
set(BISON_VERSION 3.8.2)
set(BISON_URL "https://mirror.us-midwest-1.nexcess.net/gnu/bison/bison-${BISON_VERSION}.tar.gz")
set(BISON_SHA256 06c9e13bdf7eb24d4ceb6b59205a4f67c2c7e7213119644430fe82fbd14a0abb)
