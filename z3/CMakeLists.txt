# Find Z3 installation
if(DEFINED Z3_INSTALL_DIR)
  list(PREPEND CMAKE_PREFIX_PATH "${Z3_INSTALL_DIR}")
endif()
find_package(Z3 REQUIRED)

# Variables needed in setup.py
# TODO: move all compilation commands into CMake
get_target_property(Z3_CONFIGURATIONS z3::libz3 IMPORTED_CONFIGURATIONS)
list(GET Z3_CONFIGURATIONS 0 Z3_DEFAULT_CONFIGURATION)
get_target_property(Z3_LIBRARY_LOCATION z3::libz3 IMPORTED_LOCATION_${Z3_DEFAULT_CONFIGURATION})
set(Z3_LIBRARY_LOCATION "${Z3_LIBRARY_LOCATION}" PARENT_SCOPE)

add_library(smt-switch-z3 "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_term.cpp"
)

target_include_directories(smt-switch-z3 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories(smt-switch-z3 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories(smt-switch-z3 PRIVATE ${GMP_INCLUDE_DIR})
target_link_libraries(smt-switch-z3 PUBLIC smt-switch)
target_link_libraries(smt-switch-z3 PUBLIC z3::libz3)
target_link_libraries(smt-switch-z3 PRIVATE ${GMP_LIBRARIES})
target_link_libraries(smt-switch-z3 PRIVATE ${GMPXX_LIBRARIES})

install(TARGETS smt-switch-z3 DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
