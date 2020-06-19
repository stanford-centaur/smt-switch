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
  if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
    # make sure to use the repacked cvc4 static lib if built statically
    # CVC4 was a special-case for bundling libcvc4.a into libsmt-switch-cvc4.a
    # see cvc4/CMakeLists.txt from the top-level directory
    add_dependencies(${test}.out repack-cvc4-static-lib)
  endif()
  target_link_libraries(${test}.out smt-switch smt-switch-cvc4)
  target_link_libraries(${test}.out test-deps)
  add_test(${test} ${test}.out)
endforeach()
