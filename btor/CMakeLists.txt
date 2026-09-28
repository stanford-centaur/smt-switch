add_library(
  smt-switch-btor
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/boolector_term.cpp"
  "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/memstream.c"
)
target_include_directories(
  smt-switch-btor
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)
target_link_libraries(smt-switch-btor PUBLIC smt-switch)

# memstream.c is compiled into this library, so its header is only needed
# while building it.
target_include_directories(smt-switch-btor PRIVATE "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/")

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
#
# This is deliberately build-only. An installed smt-switch cannot promise a
# consumer a Boolector source tree, so the exported target does not claim to.
# Consumers reaching the solver through boolector_factory.h are unaffected.
# The headers installed here for expert use are another matter: they include
# Boolector's own headers, boolector.h among them, which its install puts
# under include/boolector rather than where these expect. Including one of
# them downstream means putting Boolector's headers on the include path.
# SYSTEM because these are Boolector's headers, not ours.
target_include_directories(
  smt-switch-btor
  SYSTEM
  PUBLIC $<BUILD_INTERFACE:${Boolector_SOURCE_DIR}/src>
)

include(ImportedLocation)
smt_switch_imported_location(Boolector::boolector Boolector_LIBRARY)
get_target_property(Boolector_LINK_LIBRARIES Boolector::boolector INTERFACE_LINK_LIBRARIES)

# setup.py links the extension module by hand rather than through a CMake
# target, so a static build has to be told which archives sit behind this
# backend. See python/setup.py.in.
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
