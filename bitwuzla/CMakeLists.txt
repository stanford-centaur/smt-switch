add_library(
  smt-switch-bitwuzla
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_term.cpp"
)
target_include_directories(
  smt-switch-bitwuzla
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)

target_link_libraries(smt-switch-bitwuzla PUBLIC smt-switch)
find_package(Bitwuzla 0.4.0 REQUIRED)
target_link_libraries(smt-switch-bitwuzla PUBLIC Bitwuzla::bitwuzla)
# Bitwuzla 0.9.0 added interpolation. Its headers before 0.8.0 use the
# fixed-width integer types without including <cstdint>.
smt_switch_check_source_compiles(
  SMT_SWITCH_BITWUZLA_HAS_INTERPOLANTS
  TARGETS Bitwuzla::bitwuzla
  SOURCE
    "#include <cstdint>
#include <bitwuzla/cpp/bitwuzla.h>
void f(bitwuzla::Bitwuzla & b) { b.get_interpolants(std::vector<std::vector<bitwuzla::Term>>{}); }"
)
if(SMT_SWITCH_BITWUZLA_HAS_INTERPOLANTS)
  target_compile_definitions(smt-switch-bitwuzla PRIVATE SMT_SWITCH_BITWUZLA_HAS_INTERPOLANTS)
endif()
smt_switch_check_source_compiles(
  SMT_SWITCH_BITWUZLA_HEADER_STANDS_ALONE
  TARGETS Bitwuzla::bitwuzla
  SOURCE "#include <bitwuzla/cpp/bitwuzla.h>"
)
# Some systems keep the math functions outside libc, and bitwuzla uses them.
target_link_libraries(smt-switch-bitwuzla PRIVATE m)

add_library(SmtSwitch::smt-switch-bitwuzla ALIAS smt-switch-bitwuzla)
install(TARGETS smt-switch-bitwuzla EXPORT SmtSwitchBackendTargets-bitwuzla DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-bitwuzla
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
