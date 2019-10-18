add_library(smt-switch-z3 "${SMT_SWITCH_LIB_TYPE}"
	"${CMAKE_CURRENT_SOURCE_DIR}/src/z3_sort.cpp"
  )
target_include_directories (smt-switch-z3 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-z3 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-z3 PUBLIC "${Z3_HOME}/src")
target_include_directories (smt-switch-z3 PUBLIC "${Z3_HOME}/src/api")
target_include_directories (smt-switch-z3 PUBLIC "${Z3_HOME}/src/api/c++")

target_link_libraries(smt-switch-z3 "${Z3_HOME}/build/libz3.a")
target_link_libraries(smt-switch-z3 smt-switch)

install(TARGETS smt-switch-z3 DESTINATION lib)
