set(PORTFOLIO_TESTS
  test-portfolio-solver
)

foreach(test ${PORTFOLIO_TESTS})
  add_executable(${test}.out ${test}.cpp)
  target_include_directories (${test}.out PUBLIC "${PROJECT_SOURCE_DIR}/include")
  target_link_libraries(${test}.out smt-switch)
  if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
    # make sure to use the repacked cvc4 static lib if built statically
    # CVC4 was a special-case for bundling libcvc4.a into libsmt-switch-cvc4.a
    # see cvc4/CMakeLists.txt from the top-level directory
    add_dependencies(${test}.out repack-cvc4-static-lib)
  endif()
  target_link_libraries(${test}.out smt-switch smt-switch-cvc4)
  target_link_libraries(${test}.out test-deps)
  target_link_libraries(${test}.out smt-switch-msat)
  target_link_libraries(${test}.out smt-switch-msat test-deps)
  target_link_libraries(${test}.out smt-switch-yices2)
  target_link_libraries(${test}.out gtest_main)
  add_test(${test} ${test}.out)
  # add_test(NAME test_portfolio_solver_test COMMAND test_portfolio_solver)
endforeach()
