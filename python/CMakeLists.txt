# Check that scikit-build cmake files are present
if (NOT EXISTS "${PROJECT_SOURCE_DIR}/deps/scikit-build/skbuild/resources/cmake/")
  message(FATAL_ERROR "Missing scikit-build cmake files -- try running ./contrib/setup-skbuild.sh")
endif()

list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/deps/scikit-build/skbuild/resources/cmake/)

# Need to make sure libraries match the interpreter
# Our CMake files use the latest Python finding cmake modules (as of 2020)
# https://cmake.org/cmake/help/v3.12/module/FindPython.html (specifically the versioned ones
#  FindPython2 and FindPython3

# However, the Python Extensions from scikit-build still use an old version
# We need to set variables so that FindPythonInterp is not run in FindPythonExtensions
# below, but it looks in the right place for the PythonLibs
set(PYTHON_EXECUTABLE ${Python3_EXECUTABLE} CACHE STRING "Python executable")
set(PYTHONINTERP_FOUND ${Python3_Interpreter_FOUND} CACHE STRING "Whether Python interpreter is found")
set(PYTHON_VERSION_STRING ${Python3_VERSION} CACHE STRING "Python version string")
set(PYTHON_VERSION_MAJOR ${Python3_VERSION_MAJOR} CACHE STRING "Major python version")
set(PYTHON_VERSION_MINOR ${Python3_VERSION_MINOR} CACHE STRING "Minor python version")
set(PYTHON_VERSION_PATCH ${Python3_VERSION_PATCH} CACHE STRING "Patch python version")

if (Python3_Development_FOUND)
  set(PYTHON_LIBRARY "${Python3_LIBRARIES}" CACHE STRING "Python libraries")
  set(PYTHON_INCLUDE_DIR "${Python3_INCLUDE_DIRS}" CACHE STRING "Python include directories")
else()
  message(STATUS "Didn't find python library and include directory -- falling back")
  execute_process(COMMAND "${PYTHON_EXECUTABLE}" "-c"
    "from distutils import sysconfig as s;
print(s.get_python_inc(plat_specific=True));
print(s.get_config_var('LDVERSION') or s.get_config_var('VERSION'));
"
     RESULT_VARIABLE PY_SUCCESS
     OUTPUT_VARIABLE PY_VALS
     ERROR_VARIABLE  PY_ERR)

  if (NOT PY_SUCCESS MATCHES 0)
    message(FATAL "Cannot locate python library...")
  endif()

  # create a list
  string(REGEX REPLACE ";" "\\\\;" PY_VALS ${PY_VALS})
  string(REGEX REPLACE "\n" ";" PY_VALS ${PY_VALS})

  list(GET PY_VALS 0 PY_INCLUDE_DIR)
  list(GET PY_VALS 1 PY_LIB_SUFFIX)

  set(PYTHON_INCLUDE_DIR "${PY_INCLUDE_DIR}" CACHE STRING "Python include directory")

  # since cmake could not find the library, just set the name/version
  # and let the linker figure it out
  set(PYTHON_LIBRARY python${PY_LIB_SUFFIX} CACHE STRING "Python library")

endif()

include(FindPythonExtensions)

if(POLICY CMP0057)
  # For cmake >= 3.3 this policy changed the behavior of IN_LIST
  # if the policy exists, we use the NEW behavior
  cmake_policy(SET CMP0057 NEW)
endif()

find_package(Cython 0.29 REQUIRED)

include_directories()

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

set(SETUP_PY_IN "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in")
set(SETUP_PY "${CMAKE_CURRENT_BINARY_DIR}/setup.py")

configure_file(${SETUP_PY_IN} ${SETUP_PY})
file(WRITE ${CMAKE_CURRENT_BINARY_DIR}/__init__.py "")

install(TARGETS smt_switch DESTINATION lib)
