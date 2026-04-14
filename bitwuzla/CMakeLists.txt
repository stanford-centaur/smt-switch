find_package(PkgConfig REQUIRED)
pkg_check_modules(Bitwuzla REQUIRED IMPORTED_TARGET bitwuzla)

add_library(
  smt-switch-bitwuzla
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_term.cpp"
)
target_include_directories(smt-switch-bitwuzla PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_link_libraries(smt-switch-bitwuzla PUBLIC smt-switch)
target_link_libraries(smt-switch-bitwuzla PUBLIC PkgConfig::Bitwuzla)

install(TARGETS smt-switch-bitwuzla DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
