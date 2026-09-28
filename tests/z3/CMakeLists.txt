# These include backend headers, which need the Z3 headers that
# test-solvers does not pass on, so they link the backend directly.
set(z3_direct_tests z3_test)

macro(switch_add_z3_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/z3/${name}.cpp")
  if("${name}" IN_LIST z3_direct_tests)
    target_link_libraries(${name} PRIVATE smt-switch-z3)
  else()
    target_link_libraries(${name} PRIVATE test-solvers)
  endif()
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

switch_add_z3_test(z3_full)
switch_add_z3_test(z3_test)
