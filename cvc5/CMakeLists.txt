add_library(
  smt-switch-cvc5
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_term.cpp"
)
target_include_directories(
  smt-switch-cvc5
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)

target_link_libraries(smt-switch-cvc5 PUBLIC smt-switch)
# The version is checked here rather than passed to find_package, because
# cvc5's config package treats a requested version as an exact match and
# would reject every later release.
find_package(cvc5 REQUIRED)
set(CVC5_MINIMUM_VERSION 1.3.1)
if(cvc5_VERSION VERSION_LESS CVC5_MINIMUM_VERSION)
  message(
    FATAL_ERROR
    "cvc5 ${CVC5_MINIMUM_VERSION} or later is required, but ${cvc5_VERSION} "
    "was found in ${cvc5_DIR}. Point --cvc5-dir at a newer install prefix, or "
    "delete deps/cvc5 to have the pinned version built instead."
  )
endif()
target_link_libraries(smt-switch-cvc5 PUBLIC cvc5::cvc5)
# cvc5's package names gmp in its link interface as a plain library too, and
# does not find it, so saying where it is falls to us.
find_package(GMP REQUIRED)
target_link_libraries(smt-switch-cvc5 PUBLIC GMP::gmp)
# Some systems keep the math functions outside libc, and cvc5 uses them.
target_link_libraries(smt-switch-cvc5 PRIVATE m)

# Cadical and Libpoly (picpoly and picpolyxx) are also plain library names
# on the cvc5 link line, so we need to find them. They are in cvc5's own
# install prefix when auto-downloaded, so we look there first, otherwise
# they were provided by the system. find_library only learned REQUIRED in
# CMake 3.18, hence the checks.
include(ImportedLocation)
smt_switch_imported_location(cvc5::cvc5 cvc5_LIBRARY)
get_filename_component(cvc5_LIBRARY_DIR "${cvc5_LIBRARY}" DIRECTORY)
find_library(cvc5_CADICAL_LIBRARY NAMES cadical HINTS "${cvc5_LIBRARY_DIR}")
mark_as_advanced(cvc5_CADICAL_LIBRARY)
if(NOT cvc5_CADICAL_LIBRARY)
  message(FATAL_ERROR "Could not find cadical, required by cvc5")
endif()
get_filename_component(cvc5_CADICAL_LIBRARY_DIR "${cvc5_CADICAL_LIBRARY}" DIRECTORY)
target_link_directories(smt-switch-cvc5 PUBLIC $<BUILD_INTERFACE:${cvc5_CADICAL_LIBRARY_DIR}>)
find_library(cvc5_POLY_LIBRARY NAMES picpoly HINTS "${cvc5_LIBRARY_DIR}")
find_library(cvc5_POLYXX_LIBRARY NAMES picpolyxx HINTS "${cvc5_LIBRARY_DIR}")
mark_as_advanced(cvc5_POLY_LIBRARY cvc5_POLYXX_LIBRARY)
if(NOT cvc5_POLY_LIBRARY OR NOT cvc5_POLYXX_LIBRARY)
  message(FATAL_ERROR "Could not find picpoly and picpolyxx, required by cvc5")
endif()
get_filename_component(cvc5_POLY_LIBRARY_DIR "${cvc5_POLY_LIBRARY}" DIRECTORY)
target_link_directories(smt-switch-cvc5 PUBLIC $<BUILD_INTERFACE:${cvc5_POLY_LIBRARY_DIR}>)

# setup.py links the extension module by hand rather than through a CMake
# target, so a static build has to be told which archives sit behind this
# backend. See python/setup.py.in. GMP is left out; setup.py adds it for
# whichever backends need it.
if(SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  set(
    CVC5_STATIC_LINK_ARGS
    "${cvc5_LIBRARY}"
    "${cvc5_CADICAL_LIBRARY}"
    "${cvc5_POLYXX_LIBRARY}"
    "${cvc5_POLY_LIBRARY}"
    PARENT_SCOPE
  )
endif()

add_library(SmtSwitch::smt-switch-cvc5 ALIAS smt-switch-cvc5)
install(TARGETS smt-switch-cvc5 EXPORT SmtSwitchBackendTargets-cvc5 DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-cvc5
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
