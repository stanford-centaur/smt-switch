# These include backend headers, which need the MathSAT headers that
# test-solvers does not pass on, so they link the backend directly.
set(msat_direct_tests msat-assumption-clauses msat-constructors)

macro(switch_add_msat_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/msat/${name}.cpp")
  if("${name}" IN_LIST msat_direct_tests)
    target_link_libraries(${name} PRIVATE smt-switch-msat)
  else()
    target_link_libraries(${name} PRIVATE test-solvers)
  endif()
  target_link_libraries(${name} PRIVATE exec-utils)
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
  add_test(NAME ${name} COMMAND ${name})
endmacro()

switch_add_msat_test(msat-array-values)
switch_add_msat_test(msat-assumption-clauses)
switch_add_msat_test(msat-constructors)
switch_add_msat_test(msat-interpolator-options)
switch_add_msat_test(msat-printing)
