find_package(Threads REQUIRED)
find_package(GMP REQUIRED)
find_package(Yices2 REQUIRED)

add_library(
  smt-switch-yices2
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_term.cpp"
)

add_library(SmtSwitch::smt-switch-yices2 ALIAS smt-switch-yices2)

target_include_directories(
  smt-switch-yices2
  PUBLIC $<BUILD_INTERFACE:${CMAKE_CURRENT_SOURCE_DIR}/include> $<INSTALL_INTERFACE:include>
)
target_link_libraries(smt-switch-yices2 GMP::gmp)
target_link_libraries(smt-switch-yices2 Yices2::yices)
target_link_libraries(smt-switch-yices2 smt-switch)
target_link_libraries(smt-switch-yices2 Threads::Threads)

# setup.py links the extension module by hand rather than through a CMake
# target, so a static build has to be told which archive sits behind this
# backend. See python/setup.py.in.
set(YICES2_STATIC_LINK_ARGS "${Yices2_LIBRARY}" PARENT_SCOPE)

install(TARGETS smt-switch-yices2 EXPORT SmtSwitchBackendTargets-yices2 DESTINATION lib)
install(
  EXPORT SmtSwitchBackendTargets-yices2
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
