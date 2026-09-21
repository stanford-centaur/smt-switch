find_package(Z3 REQUIRED)

find_package(GMP REQUIRED COMPONENTS gmpxx)

# Variables needed in setup.py
# TODO: move all compilation commands into CMake
include(ImportedLocation)
smt_switch_imported_location(z3::libz3 Z3_LIBRARY_LOCATION)
set(Z3_LIBRARY_LOCATION "${Z3_LIBRARY_LOCATION}" PARENT_SCOPE)

add_library(
  smt-switch-z3
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/z3_term.cpp"
)

# z3_solver.cpp has used std::make_unique and the `s` string literal suffix,
# both C++14, since long before this floor was written, and the headers it
# installs stay C++11. PRIVATE, so a consumer inherits nothing from it.
target_compile_features(smt-switch-z3 PRIVATE cxx_std_14)

target_include_directories(smt-switch-z3 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_link_libraries(smt-switch-z3 PUBLIC smt-switch)
target_link_libraries(smt-switch-z3 PUBLIC z3::libz3)
target_link_libraries(smt-switch-z3 PRIVATE GMP::gmpxx)

install(TARGETS smt-switch-z3 DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
