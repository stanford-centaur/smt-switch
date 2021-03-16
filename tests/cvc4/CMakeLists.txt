macro(switch_add_cvc4_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/cvc4/${name}.cpp")
  target_link_libraries(${name} gtest_main)
  target_link_libraries(${name} test-deps)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

# these tests don't use GoogleTest yet
# TODO move old tests to Google Test infrastructure
switch_add_cvc4_test(cvc4-arrays)
switch_add_cvc4_test(cvc4-data-structures)
switch_add_cvc4_test(cvc4-indexed-op-tests)
switch_add_cvc4_test(cvc4-int-arithmetic)
switch_add_cvc4_test(cvc4_test)
switch_add_cvc4_test(cvc4-tests)
switch_add_cvc4_test(cvc4-incremental)
switch_add_cvc4_test(cvc4-interpolants)
switch_add_cvc4_test(cvc4-interpolants-api)
switch_add_cvc4_test(cvc4-transfer)
switch_add_cvc4_test(cvc4-neg-numbers)
switch_add_cvc4_test(cvc4-printing)

# Google Test
switch_add_cvc4_test(cvc4-term-iter)
