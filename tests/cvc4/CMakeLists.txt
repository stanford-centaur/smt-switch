set(CVC4_TESTS
  cvc4-arrays
  cvc4-data-structures
  cvc4-indexed-op-tests
  cvc4-int-arithmetic
  cvc4_test
  cvc4-tests
  cvc4-incremental
  # cvc4-transfer # need to be able to get operator for rebuilding
  cvc4-neg-numbers
  cvc4-printing
)

foreach(test ${CVC4_TESTS})
  add_executable(${test}.out ${test}.cpp)
  target_link_libraries(${test}.out smt-switch smt-switch-cvc4)
  target_link_libraries(${test}.out test-deps)
  add_test(${test} ${test}.out)
endforeach()
