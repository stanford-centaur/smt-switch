find_package(MathSAT REQUIRED)

add_library(
  smt-switch-msat
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_term.cpp"
)
target_include_directories(smt-switch-msat PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_link_libraries(smt-switch-msat PUBLIC MathSAT::MathSAT)
target_link_libraries(smt-switch-msat smt-switch)

install(TARGETS smt-switch-msat DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
