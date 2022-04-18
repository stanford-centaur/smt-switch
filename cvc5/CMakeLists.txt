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

find_library(POLYLIB REQUIRED
             NAMES libpicpoly.a
             PATHS "${CVC5_HOME}/build/deps/lib")

find_library(POLYLIBXX REQUIRED
             NAMES libpicpolyxx.a
             PATHS "${CVC5_HOME}/build/deps/lib")

find_library(CADICAL REQUIRED
             NAMES libcadical.a libcadical.so libcadical.dylib
             PATHS "${CVC5_HOME}/build/deps/lib")

target_link_libraries(smt-switch-cvc5 "${CVC5_HOME}/build/src/libcvc5.a")
target_link_libraries(smt-switch-cvc5 "${CVC5_HOME}/build/src/parser/libcvc5parser.a")
target_link_libraries(smt-switch-cvc5 "${POLYLIBXX}")
target_link_libraries(smt-switch-cvc5 "${POLYLIB}")
target_link_libraries(smt-switch-cvc5 "${CADICAL}")
target_link_libraries(smt-switch-cvc5 smt-switch)
target_link_libraries(smt-switch-cvc5 ${GMP_LIBRARIES})

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the cvc5 source and dependencies (except GMP)
  # use libtool to combine
  add_custom_command(
    OUTPUT static-smt-switch-cvc5.stamp
    COMMAND
      mkdir ssc-working && cd ssc-working &&
      # create new static library that combines them all
      ${PROJECT_SOURCE_DIR}/scripts/repack-static-lib.sh "$<TARGET_FILE_NAME:smt-switch-cvc5>" "${CVC5_HOME}/build/src/libcvc5.a" "${POLYLIBXX}" "${POLYLIB}" "${CADICAL}" "../$<TARGET_FILE_NAME:smt-switch-cvc5>" &&
      # replace the original one
      mv "$<TARGET_FILE_NAME:smt-switch-cvc5>" "../$<TARGET_FILE_NAME:smt-switch-cvc5>" &&
      # now clean up the temporary directory
      cd ../ && rm -rf ssc-working
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
