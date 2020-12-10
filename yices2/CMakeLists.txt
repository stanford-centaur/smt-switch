add_library(smt-switch-yices2 "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_term.cpp"
  )

target_include_directories (smt-switch-yices2 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-yices2 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-yices2 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/yices2/include")
target_include_directories (smt-switch-yices2 PUBLIC "${YICES2_HOME}/src/include")
target_include_directories (smt-switch-yices2 PUBLIC "${GMP_INCLUDE_DIR}")
target_link_libraries(smt-switch-yices2 "${GMP_LIBRARIES}")
target_link_libraries(smt-switch-yices2 "${YICES2_HOME}/build/lib/libyices.a")
target_link_libraries(smt-switch-yices2 smt-switch)
target_link_libraries(smt-switch-yices2 pthread)


if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the yices2 source
  # we need to unpack and repack the libraries
  add_custom_target(repack-yices2-static-lib
    ALL
    COMMAND
      mkdir smt-switch-yices2 && cd smt-switch-yices2 && ar -x "../$<TARGET_FILE_NAME:smt-switch-yices2>" && cd ../ &&
      mkdir yices2 && cd yices2 && ar -x "${YICES2_HOME}/build/lib/libyices.a" && cd ../ &&
      ar -qc "$<TARGET_FILE_NAME:smt-switch-yices2>" ./yices2/*.o ./smt-switch-yices2/*.o &&
      # now clean up
      rm -rf smt-switch-yices2 yices2
    DEPENDS
      smt-switch-yices2
    )
endif()

install(TARGETS smt-switch-yices2 DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
