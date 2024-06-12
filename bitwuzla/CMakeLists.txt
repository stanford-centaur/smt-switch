set(CMAKE_POSITION_INDEPENDENT_CODE ON)

# Find Bitwuzla installation
list(PREPEND CMAKE_PREFIX_PATH "${BITWUZLA_DIR}")
find_package(PkgConfig REQUIRED)
pkg_check_modules(BITWUZLA REQUIRED bitwuzla)

add_library(smt-switch-bitwuzla "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/bitwuzla_term.cpp"
  )

target_include_directories (smt-switch-bitwuzla PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-bitwuzla PUBLIC "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/")
target_include_directories (smt-switch-bitwuzla PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-bitwuzla PUBLIC ${BITWUZLA_INCLUDE_DIRS})

target_link_libraries(smt-switch-bitwuzla smt-switch)
target_link_libraries(smt-switch-bitwuzla ${BITWUZLA_LDFLAGS})

install(TARGETS smt-switch-bitwuzla DESTINATION lib)
# install headers -- for expert use only
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING PATTERN "*.h")
