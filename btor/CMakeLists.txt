set(CMAKE_POSITION_INDEPENDENT_CODE ON)

find_package(Boolector REQUIRED)

# Boolector's package declares libbtor2parser.a and libcadical.a in the link
# interface of Boolector::boolector, so linking that one target is enough.
include(ImportedLocation)
smt_switch_imported_location(Boolector::boolector Boolector_LIBRARY)
get_target_property(Boolector_LINK_LIBRARIES Boolector::boolector INTERFACE_LINK_LIBRARIES)

add_library(
  smt-switch-btor
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_term.cpp"
  "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/memstream.c"
)
target_include_directories(smt-switch-btor PUBLIC "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/")
target_include_directories(smt-switch-btor PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
# boolector_term.h needs btorcore.h, btornode.h and utils/btornodeiter.h,
# which Boolector does not install: only boolector.h and btortypes.h are part
# of its public API. Hence the source tree in addition to the package.
target_include_directories(smt-switch-btor PUBLIC "${Boolector_SOURCE_DIR}/src")

target_link_libraries(smt-switch-btor Boolector::boolector)
target_link_libraries(smt-switch-btor smt-switch)
target_link_libraries(smt-switch-btor pthread)
target_link_libraries(smt-switch-btor m)

if(SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the boolector source
  # we need to unpack and repack the libraries
  add_custom_command(
    OUTPUT static-smt-switch-btor.stamp
    COMMAND
      mkdir smt-switch-btor-working && cd smt-switch-btor-working &&
      # create new static library that combines them all
      ${PROJECT_SOURCE_DIR}/scripts/repack-static-lib.sh "$<TARGET_FILE_NAME:smt-switch-btor>"
      "${Boolector_LIBRARY}" ${Boolector_LINK_LIBRARIES} "../$<TARGET_FILE_NAME:smt-switch-btor>"
      &&
      # replace the original one
      mv "$<TARGET_FILE_NAME:smt-switch-btor>" "../$<TARGET_FILE_NAME:smt-switch-btor>" &&
      # now clean up
      cd .. && rm -rf smt-switch-btor-working
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-btor.stamp
    DEPENDS smt-switch-btor
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    VERBATIM
  )

  add_custom_target(repack-btor-static-lib ALL DEPENDS static-smt-switch-btor.stamp)
endif()

install(TARGETS smt-switch-btor DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
