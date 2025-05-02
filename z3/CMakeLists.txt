# Find Z3 installation
if(DEFINED Z3_INSTALL_DIR)
  list(PREPEND CMAKE_PREFIX_PATH "${Z3_INSTALL_DIR}")
endif()
find_package(PkgConfig REQUIRED)
pkg_check_modules(Z3 REQUIRED z3)

add_library(smt-switch-z3 "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_term.cpp"
)

target_include_directories(smt-switch-z3 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories(smt-switch-z3 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories(smt-switch-z3 PUBLIC ${Z3_INCLUDE_DIRS})
target_include_directories(smt-switch-z3 PRIVATE ${GMP_INCLUDE_DIR})
target_link_libraries(smt-switch-z3 PUBLIC smt-switch)
target_link_libraries(smt-switch-z3 PUBLIC ${Z3_LDFLAGS})
target_link_libraries(smt-switch-z3 PRIVATE ${GMP_LIBRARIES})
target_link_libraries(smt-switch-z3 PRIVATE ${GMPXX_LIBRARIES})

install(TARGETS smt-switch-z3 DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
