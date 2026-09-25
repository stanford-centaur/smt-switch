set(CMAKE_POSITION_INDEPENDENT_CODE ON)

find_package(GMP REQUIRED)
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
add_library(SmtSwitch::smt-switch-msat ALIAS smt-switch-msat)

target_include_directories(
  smt-switch-msat
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)
target_link_libraries(smt-switch-msat MathSAT::mathsat)
target_link_libraries(smt-switch-msat smt-switch)
target_link_libraries(smt-switch-msat GMP::gmp)

# setup.py links the extension module by hand rather than through a CMake
# target, so a static build has to be told which archive sits behind this
# backend. See python/setup.py.in.
set(MSAT_STATIC_LINK_ARGS "${MathSAT_LIBRARY}" PARENT_SCOPE)

install(TARGETS smt-switch-msat EXPORT SmtSwitchBackendTargets-msat DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-msat
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
