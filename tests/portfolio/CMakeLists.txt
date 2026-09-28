macro(switch_add_portfolio_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/portfolio/${name}.cpp")
  target_link_libraries(${name} PRIVATE test-solvers)
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

switch_add_portfolio_test(test-portfolio-solver)
