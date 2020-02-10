add_library(smt-switch-yices2 "${SMT_SWITCH_LIB_TYPE}"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_extensions.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_factory.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_solver.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_sort.cpp"
  "${CMAKE_CURRENT_SOURCE_DIR}/src/yices2_term.cpp"
  "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/memstream.c"
  )
target_include_directories (smt-switch-yices2 PUBLIC "${PROJECT_SOURCE_DIR}/include")
target_include_directories (smt-switch-yices2 PUBLIC "${PROJECT_SOURCE_DIR}/contrib/memstream-0.1/")
target_include_directories (smt-switch-yices2 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/include")
target_include_directories (smt-switch-yices2 PUBLIC "${CMAKE_CURRENT_SOURCE_DIR}/yices2/include")
target_include_directories (smt-switch-yices2 PUBLIC "${YICES2_HOME}/src")
target_include_directories (smt-switch-yices2 PUBLIC "${YICES2_HOME}/src/include")

# TODO: fix this 
# target_include_directories (smt-switch-yices2 PUBLIC "${YICES2_HOME}/gmp/include")

target_link_libraries(smt-switch-yices2 gmp)

if(UNIX AND NOT APPLE)
    # target_link_libraries(smt-switch-yices2 "${YICES2_HOME}/gmp/lib/libgmp.a")
    target_link_libraries(smt-switch-yices2 "${YICES2_HOME}/build/lib/libyices.a")
else() 
    # Should figure out why, but my Mac did not like libgmp.a
    # target_link_libraries(smt-switch-yices2 "${YICES2_HOME}/gmp/lib/libgmp.dylib")
    target_link_libraries(smt-switch-yices2 "${YICES2_HOME}/build/lib/libyices.a")
endif()


target_link_libraries(smt-switch-yices2 smt-switch)
target_link_libraries(smt-switch-yices2 pthread)

install(TARGETS smt-switch-yices2 DESTINATION lib)
