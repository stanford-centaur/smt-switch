message(WARNING "Z3 backend development is still in progress and not yet ready for use")
add_library(smt-switch-z3 "${SMT_SWITCH_LIB_TYPE}"
  # "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_term.cpp"
  )

target_include_directories (smt-switch-z3 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-z3 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-z3 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/z3/include")
target_include_directories (smt-switch-z3 PUBLIC "${Z3_HOME}/src/include")
target_include_directories (smt-switch-z3 PUBLIC "${Z3_HOME}/src/api")
target_include_directories (smt-switch-z3 PUBLIC "${Z3_HOME}/src/api/c++")
target_link_libraries(smt-switch-z3 "${Z3_HOME}/build/libz3.a")
target_link_libraries(smt-switch-z3 smt-switch)
target_link_libraries(smt-switch-z3 pthread)


if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the z3 source
  # we need to unpack and repack the libraries
  add_custom_target(repack-z3-static-lib
    ALL
    COMMAND
      mkdir smt-switch-z3 && cd smt-switch-z3 && ar -x "../$<TARGET_FILE_NAME:smt-switch-z3>" && cd ../ &&
      mkdir z3 && cd z3 && ar -x "${Z3_HOME}/build/libz3.a" && cd ../ &&
      ar -qc "$<TARGET_FILE_NAME:smt-switch-z3>" ./z3/*.o ./smt-switch-z3/*.o &&
      # now clean up
      rm -rf smt-switch-z3 z3
    DEPENDS
      smt-switch-z3
    )
endif()

install(TARGETS smt-switch-z3 DESTINATION lib)
