find_package(cvc5 REQUIRED)

add_library(
  smt-switch-cvc5
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_term.cpp"
)
target_include_directories(smt-switch-cvc5 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_link_libraries(smt-switch-cvc5 PUBLIC cvc5::cvc5)
target_link_libraries(smt-switch-cvc5 PUBLIC smt-switch)

install(TARGETS smt-switch-cvc5 DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
