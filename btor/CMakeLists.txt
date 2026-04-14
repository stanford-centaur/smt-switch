find_package(Boolector REQUIRED)

# We use some internal boolector headers so need access to the sources.
if(NOT DEFINED BTOR_HOME)
  set(BTOR_HOME "${PROJECT_SOURCE_DIR}/deps/boolector")
endif()

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
target_include_directories(smt-switch-btor PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories(smt-switch-btor PUBLIC "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/")
target_include_directories(smt-switch-btor PUBLIC "${BTOR_HOME}/src")
target_link_libraries(smt-switch-btor smt-switch)
target_link_libraries(smt-switch-btor Boolector::boolector)

install(TARGETS smt-switch-btor DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
