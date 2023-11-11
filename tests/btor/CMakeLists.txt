macro(switch_add_btor_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/btor/${name}.cpp")
  target_link_libraries(${name} gtest gtest_main)
  target_link_libraries(${name} test-deps)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

# these tests don't use GoogleTest yet
# TODO move old tests to Google Test infrastructure
switch_add_btor_test(btor-arrays)
switch_add_btor_test(btor-data-structures)
switch_add_btor_test(btor-exceptions)
switch_add_btor_test(btor-indexed-op-tests)
switch_add_btor_test(btor-tests)
switch_add_btor_test(btor-incremental)
switch_add_btor_test(btor-transfer)
switch_add_btor_test(btor-negation)
switch_add_btor_test(btor-const-arrays)
switch_add_btor_test(btor-substitute)
switch_add_btor_test(btor-simple)
switch_add_btor_test(btor-array-models)
switch_add_btor_test(btor-array-empty-assignment)
switch_add_btor_test(btor-neg-numbers)

# Google Test

switch_add_btor_test(btor-opts)
