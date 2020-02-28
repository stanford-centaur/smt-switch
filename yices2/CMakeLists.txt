add_library(smt-switch-yices2 "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_term.cpp"
  )

target_include_directories (smt-switch-yices2 PUBLIC "${PROJECT_SOURCE_DIR}/include")
#target_include_directories (smt-switch-yices2 PUBLIC "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/")
target_include_directories (smt-switch-yices2 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-yices2 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/yices2/include")
target_include_directories (smt-switch-yices2 PUBLIC "${YICES2_HOME}/src/include")

target_link_libraries(smt-switch-yices2 gmp)

target_link_libraries(smt-switch-yices2 "${YICES2_HOME}/build/lib/libyices.a")


target_link_libraries(smt-switch-yices2 smt-switch)
target_link_libraries(smt-switch-yices2 pthread)

install(TARGETS smt-switch-yices2 DESTINATION lib)
