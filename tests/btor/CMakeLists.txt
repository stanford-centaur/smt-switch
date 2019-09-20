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
)

foreach(test ${BTOR_TESTS})
  add_executable(${test}.out ${test}.cpp)
  target_link_libraries(${test}.out smt-switch smt-switch-btor)
  target_include_directories (${test}.out PUBLIC "${PROJECT_SOURCE_DIR}/include")
  add_test(${test} ${test}.out)
endforeach()
