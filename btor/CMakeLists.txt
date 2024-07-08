set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_library(smt-switch-btor "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_term.cpp"
  "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/memstream.c"
  )
target_include_directories (smt-switch-btor PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-btor PUBLIC "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/")
target_include_directories (smt-switch-btor PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-btor PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/btor/include")
target_include_directories (smt-switch-btor PUBLIC "${BTOR_HOME}/src")

target_link_libraries(smt-switch-btor "${BTOR_HOME}/build/lib/libboolector.a")
target_link_libraries(smt-switch-btor "${PROJECT_SOURCE_DIR}/deps/install/lib/libcadical.a")
target_link_libraries(smt-switch-btor "${BTOR_HOME}/deps/btor2tools/build/lib/libbtor2parser.a")
target_link_libraries(smt-switch-btor smt-switch)
target_link_libraries(smt-switch-btor pthread)
target_link_libraries(smt-switch-btor m)

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the boolector source
  # we need to unpack and repack the libraries
  add_custom_command(
    OUTPUT static-smt-switch-btor.stamp
    COMMAND
      mkdir smt-switch-btor-working && cd smt-switch-btor-working &&
      # create new static library that combines them all
      ${PROJECT_SOURCE_DIR}/scripts/repack-static-lib.sh "$<TARGET_FILE_NAME:smt-switch-btor>"
        "${BTOR_HOME}/build/lib/libboolector.a"
        "${PROJECT_SOURCE_DIR}/deps/install/lib/libcadical.a"
        "${BTOR_HOME}/deps/btor2tools/build/lib/libbtor2parser.a"
        "../$<TARGET_FILE_NAME:smt-switch-btor>" &&
      # replace the original one
      mv "$<TARGET_FILE_NAME:smt-switch-btor>" "../$<TARGET_FILE_NAME:smt-switch-btor>" &&
      # now clean up
      cd .. && rm -rf smt-switch-btor-working
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-btor.stamp
    DEPENDS
      smt-switch-btor
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    VERBATIM
    )

  add_custom_target(repack-btor-static-lib
    ALL
    DEPENDS
      static-smt-switch-btor.stamp
    )
endif()

install(TARGETS smt-switch-btor DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
