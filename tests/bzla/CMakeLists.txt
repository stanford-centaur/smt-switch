macro(switch_add_bzla_legacy_test name)
  add_executable(${name} "${PROJECT_SOURCE_DIR}/tests/bzla/${name}.cpp")
  target_link_libraries(${name} PRIVATE smt-switch-bitwuzla)
  target_link_libraries(${name} PRIVATE exec-utils)
  add_test(NAME ${name} COMMAND ${name})
endmacro()

macro(switch_add_bzla_test name)
  switch_add_bzla_legacy_test(${name})
  target_link_libraries(${name} PRIVATE GTest::gtest_main)
endmacro()

# these tests don't use GoogleTest yet
# TODO move old tests to Google Test infrastructure
switch_add_bzla_legacy_test(bzla-interpolants)
switch_add_bzla_legacy_test(bzla-seq-interpolants)

switch_add_bzla_test(bzla-printing)
