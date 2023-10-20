macro(switch_add_cvc5_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/cvc5/${name}.cpp")
  target_link_libraries(${name} gtest_main)
  target_link_libraries(${name} test-deps)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

# these tests don't use GoogleTest yet
# TODO move old tests to Google Test infrastructure
switch_add_cvc5_test(cvc5-arrays)
switch_add_cvc5_test(cvc5-data-structures)
switch_add_cvc5_test(cvc5-indexed-op-tests)
switch_add_cvc5_test(cvc5-int-arithmetic)
switch_add_cvc5_test(cvc5_test)
switch_add_cvc5_test(cvc5-tests)
switch_add_cvc5_test(cvc5-incremental)
switch_add_cvc5_test(cvc5-interpolants)
switch_add_cvc5_test(cvc5-interpolants-api)
switch_add_cvc5_test(cvc5-transfer)
switch_add_cvc5_test(cvc5-neg-numbers)
switch_add_cvc5_test(cvc5-printing)
switch_add_cvc5_test(cvc5-str)

# Google Test
switch_add_cvc5_test(cvc5-term-iter)
