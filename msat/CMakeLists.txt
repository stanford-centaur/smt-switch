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
# mathsat.h gives no version to compare, so the minimum is checked through
# msat_type_id, which sorts are hashed by and 5.6.8 added.
smt_switch_check_source_compiles(
  SMT_SWITCH_MSAT_HAS_TYPE_ID
  TARGETS MathSAT::mathsat GMP::gmp
  SOURCE "#include <mathsat.h>\nsize_t id(msat_type t) { return msat_type_id(t); }"
)
if(NOT SMT_SWITCH_MSAT_HAS_TYPE_ID)
  message(FATAL_ERROR "smt-switch needs MathSAT 5.6.8 or newer")
endif()

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
