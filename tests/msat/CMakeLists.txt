set(MSAT_TESTS
  msat-tests
  msat-arrays
  msat-arrays2
  msat-data-structures
  msat-incremental
  msat-traversal
  msat-int-arithmetic
  msat-transfer
  msat-substitute
  msat-indexed-op-tests
  msat-array-models
  msat-ext-ops
  msat-interpolants
)

foreach(test ${MSAT_TESTS})
  add_executable(${test}.out ${test}.cpp)
  target_include_directories (${test}.out PUBLIC "${PROJECT_SOURCE_DIR}/include")
  target_link_libraries(${test}.out smt-switch)
  target_link_libraries(${test}.out smt-switch-msat)
  add_test(${test} ${test}.out)
endforeach()
