macro(switch_add_yices2_legacy_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/yices2/${name}.cpp")
  target_link_libraries(${name} smt-switch-yices2)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

macro(switch_add_yices2_test name)
  switch_add_yices2_legacy_test(${name})
  target_link_libraries(${name} GTest::gtest_main)
endmacro()

# these tests don't use GoogleTest yet
# TODO move old tests to Google Test infrastructure
switch_add_yices2_legacy_test(yices2-array-models)
switch_add_yices2_legacy_test(yices2-arrays)
switch_add_yices2_legacy_test(yices2-arrays2)
switch_add_yices2_legacy_test(yices2-ext-ops)
switch_add_yices2_legacy_test(yices2-incremental)
switch_add_yices2_legacy_test(yices2-indexed-op-tests)
switch_add_yices2_legacy_test(yices2-ite-test)
switch_add_yices2_legacy_test(yices2-neg-numbers)
switch_add_yices2_legacy_test(yices2-polynomial)
switch_add_yices2_legacy_test(yices2-tests)

switch_add_yices2_test(yices2-gtest)
