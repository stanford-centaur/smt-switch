set(CMAKE_POSITION_INDEPENDENT_CODE ON)

add_library(smt-switch-cvc4 "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/cvc4_term.cpp"
  )
target_include_directories (smt-switch-cvc4 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/cvc4/include")
target_include_directories (smt-switch-cvc4 PUBLIC "${CVC4_HOME}/src")
target_include_directories (smt-switch-cvc4 PUBLIC "${CVC4_HOME}/src/include")
# TEMP only until the internal kinds are no longer part of public API
target_include_directories (smt-switch-cvc4 PUBLIC "${CVC4_HOME}/build/src")

target_link_libraries(smt-switch-cvc4 "${CVC4_HOME}/build/src/libcvc4.a")
target_link_libraries(smt-switch-cvc4 "${CVC4_HOME}/build/src/parser/libcvc4parser.a")
target_link_libraries(smt-switch-cvc4 smt-switch)
target_link_libraries(smt-switch-cvc4 gmp)

if (SMT_SWITCH_LIB_TYPE STREQUAL STATIC)
  # we want the static library to include the cvc4 source
  # we need to unpack and repack the libraries
  # CVC4 was trickier because unpacking and repacking with ar seemed to lose info
  # This uses a bash script that pipes and MRI command to ar
  # It creates a new version of the static library and replaces the existing one
  add_custom_target(repack-cvc4-static-lib
    ALL
    COMMAND
      mkdir smt-switch-cvc4 && cd smt-switch-cvc4 &&
      "${PROJECT_SOURCE_DIR}/scripts/repack-static-lib.sh"
      "$<TARGET_FILE_NAME:smt-switch-cvc4>"
      "${CVC4_HOME}/build/src/libcvc4.a"
      "${CVC4_HOME}/build/src/parser/libcvc4parser.a"
      "${CMAKE_CURRENT_BINARY_DIR}/$<TARGET_FILE_NAME:smt-switch-cvc4>" &&
      rm "../$<TARGET_FILE_NAME:smt-switch-cvc4>" && mv "./$<TARGET_FILE_NAME:smt-switch-cvc4>" ../ &&
      # now clean up
      cd ../ && rm -rf smt-switch-cvc4
    DEPENDS
      smt-switch-cvc4
    )
endif()

install(TARGETS smt-switch-cvc4 DESTINATION lib)
