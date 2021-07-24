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
target_link_libraries(smt-switch-btor "${BTOR_HOME}/deps/cadical/build/libcadical.a")
target_link_libraries(smt-switch-btor "${BTOR_HOME}/deps/btor2tools/build/libbtor2parser.a")
target_link_libraries(smt-switch-btor smt-switch)
target_link_libraries(smt-switch-btor pthread)
target_link_libraries(smt-switch-btor m)

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the boolector source
  # we need to unpack and repack the libraries
  add_custom_target(repack-btor-static-lib
    ALL
    COMMAND
      mkdir smt-switch-btor && cd smt-switch-btor && ar -x "../$<TARGET_FILE_NAME:smt-switch-btor>" && cd ../ &&
      mkdir boolector && cd boolector && ar -x "${BTOR_HOME}/build/lib/libboolector.a" &&
      ar -x "${BTOR_HOME}/deps/cadical/build/libcadical.a" &&
      ar -x "${BTOR_HOME}/deps/btor2tools/build/libbtor2parser.a" && cd ../ &&
      ar -qc "$<TARGET_FILE_NAME:smt-switch-btor>" ./boolector/*.o ./smt-switch-btor/*.o &&
      # now clean up
      rm -rf smt-switch-btor boolector
    DEPENDS
      smt-switch-btor
    )
endif()

install(TARGETS smt-switch-btor DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
