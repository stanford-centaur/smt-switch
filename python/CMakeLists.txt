if(POLICY CMP0057)
  # For cmake >= 3.3 this policy changed the behavior of IN_LIST
  # if the policy exists, we use the NEW behavior
  cmake_policy(SET CMP0057 NEW)
endif()

find_package(PythonExtensions REQUIRED)
find_package(Cython 0.29 REQUIRED)

if (USE_PYTHON2)
  message("-- We understand: it's hard to let go. We'll try to use Python2, but it's not really supported, so no promises.")
  find_package(PythonInterp 2.7 REQUIRED)
else()
  find_package(PythonInterp 3 REQUIRED)
endif()

include_directories()

add_cython_target(smt_switch CXX)

add_library(smt_switch MODULE ${smt_switch})

include_directories("${PROJECT_SOURCE_DIR}/include")
target_link_libraries(smt_switch smt-switch ${PYTHON_LIBRARIES})

# generate necessary collateral here
include_directories(${CMAKE_CURRENT_LIST_DIR})     # For generated files
set(GEN_OPTIONS --template-dir ${PROJECT_SOURCE_DIR}/python/ --dest-dir ${CMAKE_CURRENT_LIST_DIR})

if (BUILD_BTOR)
  include_directories("${PROJECT_SOURCE_DIR}/btor/include")
  target_link_libraries(smt_switch smt-switch-btor)
  set(GEN_OPTIONS ${GEN_OPTIONS} --btor)
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

add_custom_target(gen-smt-switch-imp
  ALL
  COMMAND
    ${PYTHON_EXECUTABLE}
    ${CMAKE_CURRENT_LIST_DIR}/gen-smt-switch-imp.py
    ${GEN_OPTIONS}
  DEPENDS
    gen-smt-switch-imp.py
  COMMENT
    "Generate smt_switch_imp.{pxd,pxi}"
  )

python_extension_module(smt_switch)

set(SETUP_PY_IN "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in")
set(SETUP_PY "${CMAKE_CURRENT_BINARY_DIR}/setup.py")

configure_file(${SETUP_PY_IN} ${SETUP_PY})

install(TARGETS smt_switch DESTINATION lib)
