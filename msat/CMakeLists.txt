add_library(
  smt-switch-msat
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_term.cpp"
)
target_include_directories(
  smt-switch-msat
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)
target_link_libraries(smt-switch-msat PUBLIC smt-switch)

find_package(MathSAT REQUIRED)
target_link_libraries(smt-switch-msat PUBLIC MathSAT::mathsat)

# MathSAT depends on libgmp, but there is no interface that exposes this to
# us. Public because mathsat.h includes <gmp.h>, so anyone who compiles
# against this backend's headers needs GMP's as well.
find_package(GMP REQUIRED)
target_link_libraries(smt-switch-msat PUBLIC GMP::gmp)

# setup.py links the extension module by hand rather than through a CMake
# target, so a static build has to be told which archive sits behind this
# backend. See python/setup.py.in.
set(MSAT_STATIC_LINK_ARGS "${MathSAT_LIBRARY}" PARENT_SCOPE)

add_library(SmtSwitch::smt-switch-msat ALIAS smt-switch-msat)
install(TARGETS smt-switch-msat EXPORT SmtSwitchBackendTargets-msat DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-msat
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
