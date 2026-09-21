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

if(SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the yices2 source
  # we need to unpack and repack the libraries
  add_custom_command(
    OUTPUT static-smt-switch-yices2.stamp
    COMMAND
      mkdir ssy-working && cd ssy-working && ${PROJECT_SOURCE_DIR}/scripts/repack-static-lib.sh
      "$<TARGET_FILE_NAME:smt-switch-yices2>" "${Yices2_LIBRARY}"
      "../$<TARGET_FILE_NAME:smt-switch-yices2>" && mv "$<TARGET_FILE_NAME:smt-switch-yices2>"
      "../$<TARGET_FILE_NAME:smt-switch-yices2>" && cd .. && rm -rf ssy-working
    COMMAND ${CMAKE_COMMAND} -E touch static-smt-switch-yices2.stamp
    DEPENDS smt-switch-yices2
  )
  add_custom_target(repack-yices2-static-lib ALL DEPENDS static-smt-switch-yices2.stamp)
endif()

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
