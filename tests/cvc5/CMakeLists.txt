macro(switch_add_cvc5_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/cvc5/${name}.cpp")
  target_include_directories(${name} PRIVATE "${PROJECT_SOURCE_DIR}/cvc5/include")
  target_include_directories(${name} PRIVATE "${PROJECT_SOURCE_DIR}/deps/install/include")
  target_include_directories(${name} PRIVATE "${CVC5_HOME}/include")
  target_include_directories(${name} PRIVATE "${CVC5_HOME}/build/include")
  target_link_libraries(${name} GTest::gtest_main)
  target_link_libraries(${name} test-deps)
  add_test(NAME ${name} COMMAND ${name})
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
switch_add_cvc5_test(cvc5-str)

# Google Test
switch_add_cvc5_test(cvc5-printing)
switch_add_cvc5_test(cvc5-term-iter)
