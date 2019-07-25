add_library(smt-switch-cvc4 SHARED
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_fun.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_term.cpp"
  )
target_include_directories (smt-switch-cvc4 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/btor/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CVC4_HOME}/src")
target_include_directories (smt-switch-cvc4 PUBLIC "${CVC4_HOME}/src/include")

target_link_libraries(smt-switch-cvc4 "${CVC4_HOME}/build/src/libcvc4.a")
target_link_libraries(smt-switch-cvc4 "${CVC4_HOME}/build/src/parser/libcvc4parser.a")
target_link_libraries(smt-switch-cvc4 smt-switch)
target_link_libraries(smt-switch-cvc4 gmp)

install(TARGETS smt-switch-cvc4 DESTINATION lib)
