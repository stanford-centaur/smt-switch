# These include backend headers, which need the Boolector headers that
# test-solvers does not pass on, so they link the backend directly.
set(btor_direct_tests btor-handle)

macro(switch_add_btor_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/btor/${name}.cpp")
  if("${name}" IN_LIST btor_direct_tests)
    target_link_libraries(${name} PRIVATE smt-switch-btor)
  else()
    target_link_libraries(${name} PRIVATE test-solvers)
  endif()
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

switch_add_btor_test(btor-bv-values)
switch_add_btor_test(btor-exceptions)
switch_add_btor_test(btor-handle)
switch_add_btor_test(btor-negation)
switch_add_btor_test(btor-opts)
switch_add_btor_test(btor-reset)
