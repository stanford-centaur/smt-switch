set(Z3_TESTS
  z3_test
)

foreach(test ${Z3_TESTS})
  add_executable(${test}.out ${test}.cpp)
  target_include_directories (${test}.out PUBLIC "${PROJECT_SOURCE_DIR}/include")
  target_link_libraries(${test}.out smt-switch)
  target_link_libraries(${test}.out smt-switch-z3)
  add_test(${test} ${test}.out)
endforeach()
