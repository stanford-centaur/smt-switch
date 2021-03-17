set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_library(smt-switch-msat "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_term.cpp"
  )
target_include_directories (smt-switch-msat PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-msat PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-msat PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/msat/include")
target_include_directories (smt-switch-msat PUBLIC "${MSAT_HOME}/include/")
target_include_directories (smt-switch-msat PUBLIC "${GMP_INCLUDE_DIR}")

target_link_libraries(smt-switch-msat "${MSAT_HOME}/lib/libmathsat.a")
target_link_libraries(smt-switch-msat smt-switch)
target_link_libraries(smt-switch-msat ${GMP_LIBRARIES})
target_link_libraries(smt-switch-msat ${GMPXX_LIBRARIES})

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the mathsat source
  # we need to unpack and repack the libraries
  # newer versions of mathsat (5.6.4+) have the same issue as cvc4 where
  # unpacking and repacking with ar seemed to lose info (missing symbols)
  # the work around is to just copy libmathsat.a and add to it
  add_custom_command(
    OUTPUT static-smt-switch-msat.stamp
    COMMAND
    mkdir ssm && cd ssm &&
    ar -x "../$<TARGET_FILE_NAME:smt-switch-msat>" && cd ../
    && rm "$<TARGET_FILE_NAME:smt-switch-msat>" &&
    # copy the mathsat static library to libsmt-switch-msat.a
    cp "${MSAT_HOME}/lib/libmathsat.a" "$<TARGET_FILE_NAME:smt-switch-msat>" &&
    # add the smt-switch-msat object files to the static library
    bash -c "ar -rs $<TARGET_FILE_NAME:smt-switch-msat> ./ssm/*.o"
    &&
    # now clean up the temporary directory
    rm -rf ssm
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-msat.stamp
    DEPENDS
      smt-switch-msat
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    VERBATIM
    )

  add_custom_target(
    repack-msat-static-lib ALL
    DEPENDS static-smt-switch-msat.stamp
    )
endif()

install(TARGETS smt-switch-msat DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
