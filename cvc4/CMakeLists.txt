set(CMAKE_POSITION_INDEPENDENT_CODE ON)

find_library(LIBRT rt)

add_library(smt-switch-cvc4 "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_term.cpp"
  )
target_include_directories (smt-switch-cvc4 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/cvc4/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CVC4_HOME}/src")
target_include_directories (smt-switch-cvc4 PUBLIC "${CVC4_HOME}/src/include")
# TEMP only until the internal kinds are no longer part of public API
target_include_directories (smt-switch-cvc4 PUBLIC "${CVC4_HOME}/build/src")
target_include_directories (smt-switch-cvc4 PUBLIC ${GMP_INCLUDE_DIR})

if (LIBRT)
  target_link_libraries(smt-switch-cvc4 LIBRT)
endif()

target_link_libraries(smt-switch-cvc4 "${CVC4_HOME}/build/src/libcvc4.a")
target_link_libraries(smt-switch-cvc4 "${CVC4_HOME}/build/src/parser/libcvc4parser.a")
target_link_libraries(smt-switch-cvc4 smt-switch)
target_link_libraries(smt-switch-cvc4 ${GMP_LIBRARIES})

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the cvc4 source
  # we need to unpack and repack the libraries
  # CVC4 was trickier because unpacking and repacking with ar seemed to lose info
  # the work around is to just copy libcvc4.a and add to it
  add_custom_command(
    OUTPUT static-smt-switch-cvc4.stamp
    COMMAND
      mkdir ssc && cd ssc &&
      ar -x "../$<TARGET_FILE_NAME:smt-switch-cvc4>" && cd ../
      && rm "$<TARGET_FILE_NAME:smt-switch-cvc4>" &&
      # copy the cvc4 static library to libsmt-switch-cvc4.a
      cp "${CVC4_HOME}/build/src/libcvc4.a" "$<TARGET_FILE_NAME:smt-switch-cvc4>" &&
      # add the smt-switch-cvc4 object files to the static library
      bash -c "ar -rs $<TARGET_FILE_NAME:smt-switch-cvc4> ./ssc/*.o"
      &&
      # now clean up the temporary directory
      rm -rf ssc
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-cvc4.stamp
    DEPENDS
      smt-switch-cvc4
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    VERBATIM
    )

  add_custom_target(
    repack-cvc4-static-lib ALL
    DEPENDS static-smt-switch-cvc4.stamp
    )
endif()

install(TARGETS smt-switch-cvc4 DESTINATION lib)
