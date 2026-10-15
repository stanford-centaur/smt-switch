add_library(
  smt-switch-z3
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_term.cpp"
)
target_include_directories(
  smt-switch-z3
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)

target_link_libraries(smt-switch-z3 PUBLIC smt-switch)
find_package(Z3 REQUIRED ${SMT_SWITCH_Z3_FIND_ARGS})
target_link_libraries(smt-switch-z3 PUBLIC z3::libz3)
# A consumer's find_dependency would otherwise load whichever libz3 its own
# settings favour, so the package config asks for the one used here.
get_target_property(_z3_type z3::libz3 TYPE)
if(_z3_type STREQUAL "STATIC_LIBRARY")
  set(SMT_SWITCH_Z3_DEPENDENCY_ARGS "COMPONENTS static" PARENT_SCOPE)
elseif(_z3_type STREQUAL "SHARED_LIBRARY")
  set(SMT_SWITCH_Z3_DEPENDENCY_ARGS "COMPONENTS shared" PARENT_SCOPE)
endif()
# z3_solver.cpp uses GMP
find_package(GMP REQUIRED COMPONENTS gmpxx)
target_link_libraries(smt-switch-z3 PRIVATE GMP::gmpxx)

# Variables needed in setup.py
# TODO: move all compilation commands into CMake
include(ImportedLocation)
smt_switch_imported_location(z3::libz3 Z3_LIBRARY_LOCATION)
set(Z3_LIBRARY_LOCATION "${Z3_LIBRARY_LOCATION}" PARENT_SCOPE)

add_library(SmtSwitch::smt-switch-z3 ALIAS smt-switch-z3)
install(TARGETS smt-switch-z3 EXPORT SmtSwitchBackendTargets-z3 DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-z3
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
