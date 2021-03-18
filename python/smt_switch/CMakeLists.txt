add_cython_target(smt_switch CXX)

add_library(smt_switch MODULE ${smt_switch})

include_directories("${PROJECT_SOURCE_DIR}/include")
target_link_libraries(smt_switch smt-switch)

# generate necessary collateral here
include_directories(${CMAKE_CURRENT_LIST_DIR})     # For generated files
set(GEN_OPTIONS --dest-dir ${CMAKE_CURRENT_LIST_DIR})

if (BUILD_BTOR)
  include_directories("${PROJECT_SOURCE_DIR}/btor/include")
  target_link_libraries(smt_switch smt-switch-btor)
  set(GEN_OPTIONS ${GEN_OPTIONS} --btor)
endif()

if (BUILD_BITWUZLA)
  include_directories("${PROJECT_SOURCE_DIR}/bitwuzla/include")
  target_link_libraries(smt_switch smt-switch-bitwuzla)
  set(GEN_OPTIONS ${GEN_OPTIONS} --bitwuzla)
endif()

if (BUILD_CVC4)
  include_directories("${PROJECT_SOURCE_DIR}/cvc4/include")
  target_link_libraries(smt_switch smt-switch-cvc4)
  set(GEN_OPTIONS ${GEN_OPTIONS} --cvc4)
endif()

if (BUILD_MSAT)
  include_directories("${PROJECT_SOURCE_DIR}/msat/include")
  target_link_libraries(smt_switch smt-switch-msat)
  set(GEN_OPTIONS ${GEN_OPTIONS} --msat)
endif()

if (BUILD_YICES2)
  include_directories("${PROJECT_SOURCE_DIR}/yices2/include")
  target_link_libraries(smt_switch smt-switch-yices2)
  set(GEN_OPTIONS ${GEN_OPTIONS} --yices2)
endif()

add_custom_target(gen-smt-solver-declarations
  ALL
  COMMAND
    ${PYTHON_EXECUTABLE}
    ${CMAKE_CURRENT_LIST_DIR}/gen-smt-solver-declarations.py
    ${GEN_OPTIONS}
  DEPENDS
    gen-smt-solver-declarations.py
  COMMENT
    "Generate smt_solvers.{pxd,pxi}"
  )
python_extension_module(smt_switch)

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/__init__.py.in"
               "${CMAKE_CURRENT_BINARY_DIR}/__init__.py" COPYONLY)

file(MAKE_DIRECTORY "${CMAKE_CURRENT_BINARY_DIR}/pysmt_frontend")
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/pysmt_frontend/__init__.py"
               "${CMAKE_CURRENT_BINARY_DIR}/pysmt_frontend/__init__.py" COPYONLY)
configure_file("${CMAKE_CURRENT_SOURCE_DIR}/pysmt_frontend/pysmt_solver.py"
               "${CMAKE_CURRENT_BINARY_DIR}/pysmt_frontend/pysmt_solver.py" COPYONLY)

install(TARGETS smt_switch DESTINATION lib)
