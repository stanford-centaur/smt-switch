set(BTOR_TESTS
  btor-arrays
  btor-data-structures
  btor-exceptions
  btor-indexed-op-tests
  btor-tests
  btor-incremental
  btor-transfer
  btor-negation
  btor-const-arrays
  btor-substitute
  btor-simple
  btor-array-models
  btor-array-empty-assignment
  btor-neg-numbers
)

foreach(test ${BTOR_TESTS})
  add_executable(${test}.out ${test}.cpp)
  target_include_directories (${test}.out PUBLIC "${PROJECT_SOURCE_DIR}/include")
  target_link_libraries(${test}.out smt-switch)
  target_link_libraries(${test}.out smt-switch-btor)
  target_link_libraries(${test}.out test-deps)
  add_test(${test} ${test}.out)
endforeach()
