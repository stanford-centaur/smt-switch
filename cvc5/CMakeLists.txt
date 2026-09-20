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
    "rebuild the bundled one with contrib/setup-cvc5.sh."
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

find_library(LIBRT rt)

add_library(
  smt-switch-cvc5
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_term.cpp"
)
target_include_directories(smt-switch-cvc5 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")

if(LIBRT)
  target_link_libraries(smt-switch-cvc5 ${LIBRT})
endif()

target_link_directories(smt-switch-cvc5 PUBLIC "${cvc5_LIBRARY_DIR}")
target_link_libraries(smt-switch-cvc5 cvc5::cvc5parser)
target_link_libraries(smt-switch-cvc5 cvc5::cvc5)
target_link_libraries(smt-switch-cvc5 CaDiCaL::cadical)
target_link_libraries(smt-switch-cvc5 smt-switch)
target_link_libraries(smt-switch-cvc5 GMP::gmp)

if(SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # Repacking needs the archives themselves, which the plain library names in
  # cvc5's link interface do not give us.
  find_library(cvc5_POLY_LIBRARY REQUIRED NAMES picpoly HINTS "${cvc5_LIBRARY_DIR}")
  find_library(cvc5_POLYXX_LIBRARY REQUIRED NAMES picpolyxx HINTS "${cvc5_LIBRARY_DIR}")
  mark_as_advanced(cvc5_POLY_LIBRARY cvc5_POLYXX_LIBRARY)

  # we want the static library to include the cvc5 source and dependencies (except GMP)
  # use libtool to combine
  add_custom_command(
    OUTPUT static-smt-switch-cvc5.stamp
    COMMAND
      mkdir ssc-working && cd ssc-working &&
      # create new static library that combines them all
      ${PROJECT_SOURCE_DIR}/scripts/repack-static-lib.sh "$<TARGET_FILE_NAME:smt-switch-cvc5>"
      "${cvc5_LIBRARY}" "${cvc5_POLYXX_LIBRARY}" "${cvc5_POLY_LIBRARY}" "${CaDiCaL_LIBRARY}"
      "../$<TARGET_FILE_NAME:smt-switch-cvc5>" &&
      # replace the original one
      mv "$<TARGET_FILE_NAME:smt-switch-cvc5>" "../$<TARGET_FILE_NAME:smt-switch-cvc5>" &&
      # now clean up the temporary directory
      cd ../ && rm -rf ssc-working
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-cvc5.stamp
    DEPENDS smt-switch-cvc5
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    VERBATIM
  )

  add_custom_target(repack-cvc5-static-lib ALL DEPENDS static-smt-switch-cvc5.stamp)
endif()

install(TARGETS smt-switch-cvc5 DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
