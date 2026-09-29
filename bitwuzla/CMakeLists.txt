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
find_package(Bitwuzla REQUIRED)
target_link_libraries(smt-switch-bitwuzla PUBLIC Bitwuzla::bitwuzla)
# Some systems keep the math functions outside libc, and bitwuzla uses them.
target_link_libraries(smt-switch-bitwuzla PRIVATE m)

# Variables needed in setup.py
# TODO: move all compilation commands into CMake
set(Bitwuzla_LINK_LIBRARIES "${Bitwuzla_LINK_LIBRARIES}" PARENT_SCOPE)
set(Bitwuzla_LIBRARY_DIRS "${Bitwuzla_LIBRARY_DIRS}" PARENT_SCOPE)

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
