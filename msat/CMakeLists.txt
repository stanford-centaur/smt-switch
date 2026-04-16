set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_library(
  smt-switch-msat
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/msat_term.cpp"
)
target_include_directories(smt-switch-msat PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories(smt-switch-msat PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories(smt-switch-msat PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/msat/include")
target_include_directories(smt-switch-msat PUBLIC "${MSAT_HOME}/include/")
target_include_directories(smt-switch-msat PUBLIC "${GMP_INCLUDE_DIR}")

target_link_libraries(smt-switch-msat "${MSAT_HOME}/lib/libmathsat.a")
target_link_libraries(smt-switch-msat smt-switch)
target_link_libraries(smt-switch-msat ${GMP_LIBRARIES})
target_link_libraries(smt-switch-msat ${GMPXX_LIBRARIES})

install(TARGETS smt-switch-msat DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
