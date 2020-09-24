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

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the mathsat source
  # we need to unpack and repack the libraries
  add_custom_target(repack-msat-static-lib
    ALL
    COMMAND
      mkdir smt-switch-msat && cd smt-switch-msat && ar -x "../$<TARGET_FILE_NAME:smt-switch-msat>" && cd ../ &&
      mkdir mathsat && cd mathsat && ar -x "${MSAT_HOME}/lib/libmathsat.a" && cd ../ &&
      ar -qc "$<TARGET_FILE_NAME:smt-switch-msat>" ./mathsat/*.o ./smt-switch-msat/*.o &&
      # now clean up
      rm -rf smt-switch-msat mathsat
    DEPENDS
      smt-switch-msat
    )
endif()

install(TARGETS smt-switch-msat DESTINATION lib)
