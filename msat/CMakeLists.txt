set(CMAKE_POSITION_INDEPENDENT_CODE ON)

find_package(GMP REQUIRED COMPONENTS gmpxx)
find_package(MathSAT REQUIRED)

add_library(
  smt-switch-msat
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_term.cpp"
)
add_library(SmtSwitch::smt-switch-msat ALIAS smt-switch-msat)

target_include_directories(
  smt-switch-msat
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)
target_link_libraries(smt-switch-msat MathSAT::mathsat)
target_link_libraries(smt-switch-msat smt-switch)
target_link_libraries(smt-switch-msat GMP::gmpxx)

if(SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the mathsat source
  # we need to unpack and repack the libraries
  add_custom_command(
    OUTPUT static-smt-switch-msat.stamp
    COMMAND
      mkdir smt-switch-msat-working && cd smt-switch-msat-working &&
      # create new static library that combines them all
      ${PROJECT_SOURCE_DIR}/scripts/repack-static-lib.sh "$<TARGET_FILE_NAME:smt-switch-msat>"
      "${MathSAT_LIBRARY}" "../$<TARGET_FILE_NAME:smt-switch-msat>" &&
      # replace the original one
      mv "$<TARGET_FILE_NAME:smt-switch-msat>" "../$<TARGET_FILE_NAME:smt-switch-msat>" &&
      # now clean up the temporary directory
      cd .. && rm -rf smt-switch-msat-working
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-msat.stamp
    DEPENDS smt-switch-msat
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    VERBATIM
  )

  add_custom_target(repack-msat-static-lib ALL DEPENDS static-smt-switch-msat.stamp)
endif()

install(TARGETS smt-switch-msat EXPORT SmtSwitchBackendTargets-msat DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-msat
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
