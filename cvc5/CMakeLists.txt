set(CMAKE_POSITION_INDEPENDENT_CODE ON)

find_library(LIBRT rt)

add_library(
  smt-switch-cvc5
  "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_datatype.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc5_term.cpp"
)
target_include_directories(smt-switch-cvc5 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories(smt-switch-cvc5 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories(smt-switch-cvc5 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/cvc5/include")
target_include_directories(smt-switch-cvc5 PUBLIC "${CVC5_HOME}/src")
target_include_directories(smt-switch-cvc5 PUBLIC "${CVC5_HOME}/include")
# TEMP only until the internal kinds are no longer part of public API
target_include_directories(smt-switch-cvc5 PUBLIC "${CVC5_HOME}/build/include")
target_include_directories(smt-switch-cvc5 PUBLIC ${GMP_INCLUDE_DIR})

if(LIBRT)
  target_link_libraries(smt-switch-cvc5 ${LIBRT})
endif()

find_library(POLYLIB REQUIRED NAMES libpicpoly.a PATHS "${CVC5_HOME}/build/deps/lib")

find_library(POLYLIBXX REQUIRED NAMES libpicpolyxx.a PATHS "${CVC5_HOME}/build/deps/lib")

find_library(CADICAL REQUIRED NAMES libcadical.a libcadical.so libcadical.dylib)

target_link_libraries(smt-switch-cvc5 "${CVC5_HOME}/build/src/libcvc5.a")
target_link_libraries(smt-switch-cvc5 "${CVC5_HOME}/build/src/parser/libcvc5parser.a")
target_link_libraries(smt-switch-cvc5 "${POLYLIBXX}")
target_link_libraries(smt-switch-cvc5 "${POLYLIB}")
target_link_libraries(smt-switch-cvc5 "${CADICAL}")
target_link_libraries(smt-switch-cvc5 smt-switch)
target_link_libraries(smt-switch-cvc5 ${GMP_LIBRARIES})

install(TARGETS smt-switch-cvc5 DESTINATION lib)
# install headers -- for expert use only
install(
  DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/include/"
  DESTINATION include/smt-switch
  FILES_MATCHING
  PATTERN "*.h"
)
