# These include the Yices2 headers, which test-solvers does not pass on,
# so they link the backend directly.
set(yices2_direct_tests yices2-polynomial)

macro(switch_add_yices2_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/yices2/${name}.cpp")
  if("${name}" IN_LIST yices2_direct_tests)
    target_link_libraries(${name} PRIVATE smt-switch-yices2)
  else()
    target_link_libraries(${name} PRIVATE test-solvers)
  endif()
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

switch_add_yices2_test(yices2-array-models)
switch_add_yices2_test(yices2-get-op)
switch_add_yices2_test(yices2-gtest)
switch_add_yices2_test(yices2-incremental)
switch_add_yices2_test(yices2-indexed-op-tests)
switch_add_yices2_test(yices2-params)
switch_add_yices2_test(yices2-polynomial)
switch_add_yices2_test(yices2-tests)
