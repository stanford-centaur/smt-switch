add_library(
  smt-switch-btor
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_term.cpp"
)
target_include_directories(
  smt-switch-btor
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)

target_link_libraries(smt-switch-btor PUBLIC smt-switch)
find_package(Boolector REQUIRED)
target_link_libraries(smt-switch-btor PUBLIC Boolector::boolector)
# Boolector's quantifier solver uses pthreads, which its package omits.
find_package(Threads REQUIRED)
target_link_libraries(smt-switch-btor PRIVATE Threads::Threads)
# Some systems keep the math functions outside libc, and boolector uses them.
target_link_libraries(smt-switch-btor PRIVATE m)

# boolector_term.h needs btorcore.h, btornode.h and utils/btornodeiter.h,
# which Boolector does not install: only boolector.h and btortypes.h are part
# of its public API. Hence the source tree in addition to the package.
# This is deliberately build-only. An installed smt-switch cannot promise a
# consumer a Boolector source tree, so the exported target does not claim to.
# Consumers reaching the solver through boolector_factory.h are unaffected.
target_include_directories(
  smt-switch-btor
  SYSTEM
  PUBLIC $<BUILD_INTERFACE:${Boolector_SOURCE_DIR}/src>
)

# setup.py links the extension module by hand rather than through a CMake
# target, so a static build has to be told which archives sit behind this
# backend. See python/setup.py.in.
include(ImportedLocation)
smt_switch_imported_location(Boolector::boolector Boolector_LIBRARY)
get_target_property(Boolector_LINK_LIBRARIES Boolector::boolector INTERFACE_LINK_LIBRARIES)
set(BTOR_STATIC_LINK_ARGS "${Boolector_LIBRARY}" ${Boolector_LINK_LIBRARIES} PARENT_SCOPE)

add_library(SmtSwitch::smt-switch-btor ALIAS smt-switch-btor)
install(TARGETS smt-switch-btor EXPORT SmtSwitchBackendTargets-btor DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-btor
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
