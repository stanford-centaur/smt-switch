set(CVC4_TESTS
  cvc4-arrays
  cvc4-data-structures
  cvc4-indexed-op-tests
  cvc4-int-arithmetic
  cvc4_test
  cvc4-tests
  cvc4-incremental
  # cvc4-transfer # need to be able to get operator for rebuilding
)

foreach(test ${CVC4_TESTS})
  add_executable(${test}.out ${test}.cpp)
  target_link_libraries(${test}.out smt-switch smt-switch-cvc4)
  add_test(${test} ${test}.out)
endforeach()
