macro(switch_add_z3_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/z3/${name}.cpp")
  target_link_libraries(${name} PRIVATE smt-switch-z3)
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

switch_add_z3_test(z3_full)
switch_add_z3_test(z3_test)
