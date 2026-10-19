macro(switch_add_portfolio_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/portfolio/${name}.cpp")
  target_link_libraries(${name} PRIVATE test-solvers)
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name}_test COMMAND ${name})
  # A portfolio runs its members side by side, which other tests running
  # beside it would keep from happening.
  set_tests_properties(${name}_test PROPERTIES RUN_SERIAL TRUE)
endmacro()

switch_add_portfolio_test(test-portfolio-solver)
