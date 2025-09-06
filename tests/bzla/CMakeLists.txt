macro(switch_add_bzla_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/bzla/${name}.cpp")
  target_link_libraries(${name} gtest gtest_main)
  target_link_libraries(${name} test-deps)
  add_test(NAME ${name}_test COMMAND ${name})
endmacro()

# these tests don't use GoogleTest yet
# TODO move old tests to Google Test infrastructure
switch_add_bzla_test(bzla-interpolants)
switch_add_bzla_test(bzla-seq-interpolants)
