set(CMAKE_POSITION_INDEPENDENT_CODE ON)

find_library(LIBRT rt)

add_library(smt-switch-cvc5 "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_term.cpp"
  )
target_include_directories (smt-switch-cvc5 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-cvc5 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-cvc5 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/cvc5/include")
target_include_directories (smt-switch-cvc5 PUBLIC "${CVC5_HOME}/src")
target_include_directories (smt-switch-cvc5 PUBLIC "${CVC5_HOME}/src/include")
# TEMP only until the internal kinds are no longer part of public API
target_include_directories (smt-switch-cvc5 PUBLIC "${CVC5_HOME}/build/src")
target_include_directories (smt-switch-cvc5 PUBLIC ${GMP_INCLUDE_DIR})

if (LIBRT)
  target_link_libraries(smt-switch-cvc5 ${LIBRT})
endif()

if("${SMT_SWITCH_LIB_TYPE}" STREQUAL "SHARED")
  set(POLYFILES libpoly.so libpoly.dylib)
  set(POLYXXFILES libpolyxx.so libpolyxx.dylib)
else()
  set(POLYFILES libpoly.a)
  set(POLYXXFILES libpolyxx.a)
endif()

find_library(POLYLIB REQUIRED
             NAMES ${POLYFILES}
             PATHS "${CVC5_HOME}/build/deps/lib")

find_library(POLYLIBXX REQUIRED
             NAMES ${POLYXXFILES}
             PATHS "${CVC5_HOME}/build/deps/lib")

find_library(CADICAL REQUIRED
             NAMES libcadical.a libcadical.so libcadical.dylib
             PATHS "${CVC5_HOME}/build/deps/lib")

target_link_libraries(smt-switch-cvc5 PUBLIC "${CVC5_HOME}/build/src/libcvc5.a")
target_link_libraries(smt-switch-cvc5 PUBLIC "${CVC5_HOME}/build/src/parser/libcvc5parser.a")
target_link_libraries(smt-switch-cvc5 PUBLIC "${POLYLIBXX}")
target_link_libraries(smt-switch-cvc5 PUBLIC "${POLYLIB}")
target_link_libraries(smt-switch-cvc5 PUBLIC "${CADICAL}")
target_link_libraries(smt-switch-cvc5 PUBLIC smt-switch)
target_link_libraries(smt-switch-cvc5 PUBLIC ${GMP_LIBRARIES})

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the cvc5 source
  # we need to unpack and repack the libraries
  # cvc5 was trickier because unpacking and repacking with ar seemed to lose info
  # the work around is to just copy libcvc5.a and add to it
  add_custom_command(
    OUTPUT static-smt-switch-cvc5.stamp
    COMMAND
      mkdir ssc && cd ssc &&
      ar -x "../$<TARGET_FILE_NAME:smt-switch-cvc5>" && cd ../
      && rm "$<TARGET_FILE_NAME:smt-switch-cvc5>" &&
      # copy the cvc5 static library to libsmt-switch-cvc5.a
      cp "${CVC5_HOME}/build/src/libcvc5.a" "$<TARGET_FILE_NAME:smt-switch-cvc5>" &&
      # add the smt-switch-cvc5 object files to the static library
      bash -c "ar -rs $<TARGET_FILE_NAME:smt-switch-cvc5> ./ssc/*.o"
      &&
      # now clean up the temporary directory
      rm -rf ssc
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-cvc5.stamp
    DEPENDS
      smt-switch-cvc5
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    VERBATIM
    )

  add_custom_target(
    repack-cvc5-static-lib ALL
    DEPENDS static-smt-switch-cvc5.stamp
    )
endif()

install(TARGETS smt-switch-cvc5 DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
