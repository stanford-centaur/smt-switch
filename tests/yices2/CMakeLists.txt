set(YICES2_TESTS
  yices2-polynomial
)

foreach(test ${YICES2_TESTS})
  add_executable(${test}.out ${test}.cpp)
  target_include_directories (${test}.out PUBLIC "${PROJECT_SOURCE_DIR}/include")
  target_link_libraries(${test}.out smt-switch)
  target_link_libraries(${test}.out smt-switch-yices2)
  add_test(${test} ${test}.out)
endforeach()

#add_executable(yices2-gtest yices2-gtest.cpp)
#target_include_directories (yices2-gtest PUBLIC "${PROJECT_SOURCE_DIR}/include")
#target_link_libraries(yices2-gtest gtest_main)
#target_link_libraries(yices2-gtest smt-switch)
#target_link_libraries(yices2-gtest smt-switch-yices2)
#add_test(NAME ygt_test COMMAND yices2-gtest)
