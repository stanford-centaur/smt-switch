set(CMAKE_POSITION_INDEPENDENT_CODE ON)

set(CVC5_MINIMUM_VERSION 1.3.1)

find_package(GMP REQUIRED)
# The version is checked here rather than passed to find_package, because
# cvc5's config package treats a requested version as an exact match and
# would reject every later release.
find_package(cvc5 REQUIRED)
if(cvc5_VERSION VERSION_LESS CVC5_MINIMUM_VERSION)
  message(
    FATAL_ERROR
    "cvc5 ${CVC5_MINIMUM_VERSION} or later is required, but ${cvc5_VERSION} "
    "was found in ${cvc5_DIR}. Point --cvc5-dir at a newer install prefix, or "
    "delete deps/cvc5 to have the pinned version built instead."
  )
endif()
# cvc5's package lists cadical, picpoly and picpolyxx in its link interface as
# plain library names, so the directories holding them have to reach the link
# line. CaDiCaL::cadical carries its own; picpoly is installed next to
# libcvc5.a when cvc5 downloads it, and comes from the system otherwise.
find_package(CaDiCaL REQUIRED)

include(ImportedLocation)
smt_switch_imported_location(cvc5::cvc5 cvc5_LIBRARY)
get_filename_component(cvc5_LIBRARY_DIR "${cvc5_LIBRARY}" DIRECTORY)

add_library(
  smt-switch-cvc5
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_term.cpp"
)
add_library(SmtSwitch::smt-switch-cvc5 ALIAS smt-switch-cvc5)

# cvc5's API takes std::optional and returns std::variant, so this backend and
# the cvc5_*.h headers it installs need C++17 even though smt-switch does not.
target_compile_features(smt-switch-cvc5 PUBLIC cxx_std_17)

target_include_directories(
  smt-switch-cvc5
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)

# Build-only: the directory is where this machine's cvc5 happens to live, and
# an installed package must not hand a consumer that path. Downstream gets it
# from its own find_package(cvc5) instead.
target_link_directories(smt-switch-cvc5 PUBLIC $<BUILD_INTERFACE:${cvc5_LIBRARY_DIR}>)
# LibPoly is cvc5's private dependency, but its package names picpoly and
# picpolyxx as plain libraries without saying where they are, so we have to fix
# the link commands. cvc5's own prefix is looked in first, which is where they
# sit when libpoly was auto-downloaded; failing that they are installed
# somewhere of their own, and the search finds them there.
find_library(cvc5_POLY_LIBRARY REQUIRED NAMES picpoly HINTS "${cvc5_LIBRARY_DIR}")
find_library(cvc5_POLYXX_LIBRARY REQUIRED NAMES picpolyxx HINTS "${cvc5_LIBRARY_DIR}")
mark_as_advanced(cvc5_POLY_LIBRARY cvc5_POLYXX_LIBRARY)
get_filename_component(cvc5_POLY_LIBRARY_DIR "${cvc5_POLY_LIBRARY}" DIRECTORY)
target_link_directories(smt-switch-cvc5 PUBLIC $<BUILD_INTERFACE:${cvc5_POLY_LIBRARY_DIR}>)

target_link_libraries(smt-switch-cvc5 cvc5::cvc5parser)
target_link_libraries(smt-switch-cvc5 cvc5::cvc5)
target_link_libraries(smt-switch-cvc5 CaDiCaL::cadical)
target_link_libraries(smt-switch-cvc5 smt-switch)
target_link_libraries(smt-switch-cvc5 GMP::gmp)

# setup.py links the extension module by hand rather than through a CMake
# target, so a static build has to be told which archives sit behind this
# backend. See python/setup.py.in. GMP is left out; setup.py adds it for
# whichever backends need it.
if(SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  set(
    CVC5_STATIC_LINK_ARGS
    "${cvc5_LIBRARY}"
    "${cvc5_POLYXX_LIBRARY}"
    "${cvc5_POLY_LIBRARY}"
    "${CaDiCaL_LIBRARY}"
    PARENT_SCOPE
  )
endif()

install(TARGETS smt-switch-cvc5 EXPORT SmtSwitchBackendTargets-cvc5 DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-cvc5
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
