set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_library(smt-switch-bitwuzla "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_term.cpp"
  # "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/memstream.c"
  )
target_include_directories (smt-switch-bitwuzla PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-bitwuzla PUBLIC "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/")
target_include_directories (smt-switch-bitwuzla PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-bitwuzla PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/bitwuzla/include")
target_include_directories (smt-switch-bitwuzla PUBLIC "${BITWUZLA_HOME}/src/api/c")

target_link_libraries(smt-switch-bitwuzla "${BITWUZLA_HOME}/build/lib/libcbitwuzla.a")
target_link_libraries(smt-switch-bitwuzla "${BITWUZLA_HOME}/deps/cadical/build/libcadical.a")
target_link_libraries(smt-switch-bitwuzla "${BITWUZLA_HOME}/deps/btor2tools/build/libbtor2parser.a")
target_link_libraries(smt-switch-bitwuzla smt-switch)
target_link_libraries(smt-switch-bitwuzla pthread)
target_link_libraries(smt-switch-bitwuzla m)

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the bitwuzla source
  # we need to unpack and repack the libraries
  add_custom_target(repack-bitwuzla-static-lib
    ALL
    COMMAND
      mkdir smt-switch-bitwuzla && cd smt-switch-bitwuzla && ar -x "../$<TARGET_FILE_NAME:smt-switch-bitwuzla>" && cd ../ &&
      mkdir bitwuzla && cd bitwuzla && ar -x "${BITWUZLA_HOME}/build/lib/libcbitwuzla.a" &&
      ar -x "${BITWUZLA_HOME}/deps/cadical/build/libcadical.a" &&
      ar -x "${BITWUZLA_HOME}/deps/btor2tools/build/libbtor2parser.a" && cd ../ &&
      ar -qc "$<TARGET_FILE_NAME:smt-switch-bitwuzla>" ./bitwuzla/*.o ./smt-switch-bitwuzla/*.o &&
      # now clean up
      rm -rf smt-switch-bitwuzla bitwuzla
    DEPENDS
      smt-switch-bitwuzla
    )
endif()

install(TARGETS smt-switch-bitwuzla DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
