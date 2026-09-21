set(CMAKE_POSITION_INDEPENDENT_CODE ON)

find_package(Bitwuzla REQUIRED)

# Variables needed in setup.py
# TODO: move all compilation commands into CMake
set(Bitwuzla_LINK_LIBRARIES "${Bitwuzla_LINK_LIBRARIES}" PARENT_SCOPE)
set(Bitwuzla_LIBRARY_DIRS "${Bitwuzla_LIBRARY_DIRS}" PARENT_SCOPE)

add_library(
  smt-switch-bitwuzla
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_term.cpp"
)

add_library(SmtSwitch::smt-switch-bitwuzla ALIAS smt-switch-bitwuzla)

# Bitwuzla's C++ API takes std::optional and holds a std::variant, so this
# backend and the headers it installs need C++17 even though smt-switch does not.
target_compile_features(smt-switch-bitwuzla PUBLIC cxx_std_17)

target_include_directories(
  smt-switch-bitwuzla
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)
target_link_libraries(smt-switch-bitwuzla smt-switch)
target_link_libraries(smt-switch-bitwuzla Bitwuzla::bitwuzla)

install(TARGETS smt-switch-bitwuzla EXPORT SmtSwitchBackendTargets-bitwuzla DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-bitwuzla
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
