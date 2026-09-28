add_library(
  smt-switch-yices2
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_term.cpp"
)
target_include_directories(
  smt-switch-yices2
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)
target_link_libraries(smt-switch-yices2 PUBLIC smt-switch)

find_package(Yices2 REQUIRED)
target_link_libraries(smt-switch-yices2 PUBLIC Yices2::yices)

# Yices2 depends on libgmp, but there is no interface that exposes this to us.
find_package(GMP REQUIRED)
target_link_libraries(smt-switch-yices2 PRIVATE GMP::gmp)

# setup.py links the extension module by hand rather than through a CMake
# target, so a static build has to be told which archive sits behind this
# backend. See python/setup.py.in.
set(YICES2_STATIC_LINK_ARGS "${Yices2_LIBRARY}" PARENT_SCOPE)

add_library(SmtSwitch::smt-switch-yices2 ALIAS smt-switch-yices2)
install(TARGETS smt-switch-yices2 EXPORT SmtSwitchBackendTargets-yices2 DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-yices2
  NAMESPACE SmtSwitch::
  DESTINATION "${SMT_SWITCH_CMAKE_DIR}"
)
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
