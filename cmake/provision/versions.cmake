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

# GitHub serves a tarball of a tag and of a commit from different paths, so
# there is one of these per form. Name the repository and the ref; they put
# the rest of the URL together.
function(smt_switch_github_tag name repository tag)
  set(${name}_URL "https://github.com/${repository}/archive/refs/tags/${tag}.tar.gz" PARENT_SCOPE)
endfunction()

function(smt_switch_github_commit name repository commit)
  set(${name}_URL "https://github.com/${repository}/archive/${commit}.tar.gz" PARENT_SCOPE)
endfunction()

set(CADICAL_VERSION 2.1.3)
smt_switch_github_tag(CADICAL arminbiere/cadical rel-${CADICAL_VERSION})
set(CADICAL_SHA256 abfe890aa4ccda7b8449c7ad41acb113cfb8e7e8fbf5e49369075f9b00d70465)

set(BTOR2TOOLS_COMMIT d33c73ff1d173f1bfac8ba6b1c6d68ba62c55f8e)
smt_switch_github_commit(BTOR2TOOLS hwmcc/btor2tools ${BTOR2TOOLS_COMMIT})
set(BTOR2TOOLS_SHA256 55c0b62d42b2dbbb14ebb9e4c405d127df1a92f7bfd3f5276ab862c9f9369e26)

set(BOOLECTOR_VERSION 3.2.4)
smt_switch_github_tag(BOOLECTOR boolector/boolector ${BOOLECTOR_VERSION})
set(BOOLECTOR_SHA256 249c6dbf4e52ea6e8df1ddf7965d47f5c30f2c14905dce9b8f411756b05878bf)

set(BITWUZLA_VERSION 0.9.1)
smt_switch_github_tag(BITWUZLA bitwuzla/bitwuzla ${BITWUZLA_VERSION})
set(BITWUZLA_SHA256 42707f38900a20bb18108e426ba667560d1fd2ccce0d4f75aa60439b546488b4)

set(CVC5_VERSION 1.4.0)
smt_switch_github_tag(CVC5 cvc5/cvc5 cvc5-${CVC5_VERSION})
set(CVC5_SHA256 06c65b30693d1abf7c1393b497c799950de2833457920b9433da8e418bce9113)

set(Z3_VERSION 5.1.0)
smt_switch_github_tag(Z3 Z3Prover/z3 z3-${Z3_VERSION})
set(Z3_SHA256 c433e1add0431c5edf1644bd9951c40588024d2d288f0e4215e5fcb6e3b4277d)

set(YICES2_VERSION 2.7.0)
smt_switch_github_tag(YICES2 SRI-CSL/yices2 yices-${YICES2_VERSION})
set(YICES2_SHA256 584db72abf6643927b2c3ba98ff793f602216b452b8ff2f34a8851d35904804a)

# Not a solver. Provisioned only where the system bison is older than the
# 3.7.0 the SMT-LIB reader needs, which on macOS is the default. The one pin
# that names a release tarball rather than a generated archive.
set(BISON_VERSION 3.8.2)
set(BISON_URL "https://mirror.us-midwest-1.nexcess.net/gnu/bison/bison-${BISON_VERSION}.tar.gz")
set(BISON_SHA256 06c9e13bdf7eb24d4ceb6b59205a4f67c2c7e7213119644430fe82fbd14a0abb)
