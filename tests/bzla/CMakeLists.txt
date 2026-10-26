# These include backend headers, which need the Bitwuzla headers that
# test-solvers does not pass on, so they link the backend directly.
set(bzla_direct_tests bzla-handle)

macro(switch_add_bzla_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/bzla/${name}.cpp")
  if("${name}" IN_LIST bzla_direct_tests)
    target_link_libraries(${name} PRIVATE smt-switch-bitwuzla)
  else()
    target_link_libraries(${name} PRIVATE test-solvers)
  endif()
  target_link_libraries(${name} PRIVATE exec-utils)
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name} COMMAND ${name})
endmacro()

switch_add_bzla_test(bzla-handle)
switch_add_bzla_test(bzla-options)
switch_add_bzla_test(bzla-printing)
switch_add_bzla_test(bzla-term-manager)
