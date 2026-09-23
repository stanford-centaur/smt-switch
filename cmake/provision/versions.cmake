# Pinned versions of the dependencies this project can build for itself.
#
# Bumping one here rebuilds that dependency and everything that depends on
# it: the URL is baked into the download script ExternalProject generates,
# and that script is a dependency of the download step.
#
# A pin says where the source comes from and what it must hash to, and
# nothing else: cmake/provision/CMakeLists.txt refuses to configure without
# a checksum, and recomputing one after a bump is
#
#   cmake -P cmake/provision/refresh-hashes.cmake <name>...
#
# Tags are preferred to commits, being self-describing. A tag can be moved,
# but it cannot be moved past the checksum: the archive would change and the
# download would fail. btor2tools is pinned to a commit because that
# repository has no tags at all.
#
# Note that a GitHub /archive/ URL is generated on request rather than
# stored. GitHub guarantees the bytes only for assets a project uploads
# itself, which none of these publish, and has promised six months' notice
# before changing the archive format again. So if every GitHub pin fails
# verification at once, suspect that rather than seven bad downloads.

include("${CMAKE_CURRENT_LIST_DIR}/../Helpers.cmake")

smt_switch_pin(
  CADICAL
  GITHUB_REPO arminbiere/cadical
  TAG rel-2.1.3
  CHECKSUM abfe890aa4ccda7b8449c7ad41acb113cfb8e7e8fbf5e49369075f9b00d70465
)

smt_switch_pin(
  BTOR2TOOLS
  GITHUB_REPO hwmcc/btor2tools
  COMMIT d33c73ff1d173f1bfac8ba6b1c6d68ba62c55f8e
  CHECKSUM 55c0b62d42b2dbbb14ebb9e4c405d127df1a92f7bfd3f5276ab862c9f9369e26
)

smt_switch_pin(
  BOOLECTOR
  GITHUB_REPO boolector/boolector
  TAG 3.2.4
  CHECKSUM 249c6dbf4e52ea6e8df1ddf7965d47f5c30f2c14905dce9b8f411756b05878bf
)

smt_switch_pin(
  BITWUZLA
  GITHUB_REPO bitwuzla/bitwuzla
  TAG 0.9.1
  CHECKSUM 42707f38900a20bb18108e426ba667560d1fd2ccce0d4f75aa60439b546488b4
)

smt_switch_pin(
  CVC5
  GITHUB_REPO cvc5/cvc5
  TAG cvc5-1.4.0
  CHECKSUM 06c65b30693d1abf7c1393b497c799950de2833457920b9433da8e418bce9113
)

smt_switch_pin(
  Z3
  GITHUB_REPO Z3Prover/z3
  TAG z3-5.1.0
  CHECKSUM c433e1add0431c5edf1644bd9951c40588024d2d288f0e4215e5fcb6e3b4277d
)

smt_switch_pin(
  YICES2
  GITHUB_REPO SRI-CSL/yices2
  TAG yices-2.7.0
  CHECKSUM 584db72abf6643927b2c3ba98ff793f602216b452b8ff2f34a8851d35904804a
)

# Not a solver. Provisioned only where the system bison is older than the
# 3.7.0 the SMT-LIB reader needs, which on macOS is the default. The one pin
# that names a release tarball rather than a generated archive.
smt_switch_pin(
  BISON
  GNU_PROJECT bison
  VERSION 3.8.2
  CHECKSUM 06c9e13bdf7eb24d4ceb6b59205a4f67c2c7e7213119644430fe82fbd14a0abb
)
