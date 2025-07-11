macro(switch_add_msat_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/msat/${name}.cpp")
  target_link_libraries(${name} gtest gtest_main)
  target_link_libraries(${name} test-deps)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

# these tests don't use GoogleTest yet
# TODO move old tests to Google Test infrastructure
switch_add_msat_test(msat-tests)
switch_add_msat_test(msat-arrays)
switch_add_msat_test(msat-arrays2)
switch_add_msat_test(msat-data-structures)
switch_add_msat_test(msat-incremental)
switch_add_msat_test(msat-traversal)
switch_add_msat_test(msat-int-arithmetic)
switch_add_msat_test(msat-transfer)
switch_add_msat_test(msat-substitute)
switch_add_msat_test(msat-indexed-op-tests)
switch_add_msat_test(msat-array-models)
switch_add_msat_test(msat-ext-ops)
switch_add_msat_test(msat-interpolants)
switch_add_msat_test(msat-seq-interpolants)
switch_add_msat_test(msat-const-arrays)
switch_add_msat_test(msat-ite-test)
switch_add_msat_test(msat-neg-numbers)
switch_add_msat_test(msat-printing)
