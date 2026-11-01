add_library(
  smt-switch-cvc5
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_term.cpp"
)
target_include_directories(
  smt-switch-cvc5
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)

target_link_libraries(smt-switch-cvc5 PUBLIC smt-switch)
find_package(cvc5 1.4.0 REQUIRED)
target_link_libraries(smt-switch-cvc5 PUBLIC cvc5::cvc5)
# cvc5's package names gmp in its link interface as a plain library too, and
# does not find it, so saying where it is falls to us.
find_package(GMP REQUIRED)
target_link_libraries(smt-switch-cvc5 PUBLIC GMP::gmp)
# Some systems keep the math functions outside libc, and cvc5 uses them.
target_link_libraries(smt-switch-cvc5 PRIVATE m)

add_library(SmtSwitch::smt-switch-cvc5 ALIAS smt-switch-cvc5)
install(TARGETS smt-switch-cvc5 EXPORT SmtSwitchBackendTargets-cvc5 DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-cvc5
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
