# Check that scikit-build cmake files are present
if (NOT EXISTS "${PROJECT_SOURCE_DIR}/deps/scikit-build/skbuild/resources/cmake/")
  message(FATAL_ERROR "Missing scikit-build cmake files -- try running ./contrib/setup-skbuild.sh")
endif()

list(APPEND CMAKE_MODULE_PATH ${PROJECT_SOURCE_DIR}/deps/scikit-build/skbuild/resources/cmake/)

include(FindPythonExtensions)

if(POLICY CMP0057)
  # For cmake >= 3.3 this policy changed the behavior of IN_LIST
  # if the policy exists, we use the NEW behavior
  cmake_policy(SET CMP0057 NEW)
endif()

find_package(Cython 0.29 REQUIRED)

set(SETUP_PY_IN "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in")
set(SETUP_PY "${CMAKE_CURRENT_BINARY_DIR}/setup.py")
configure_file(${SETUP_PY_IN} ${SETUP_PY})

add_subdirectory(smt_switch)
