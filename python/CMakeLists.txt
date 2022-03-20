# Note: using same pattern used in cvc5 for scikit-build / python module checking
# Check if given Python module is installed and raises a FATAL_ERROR error
# if the module cannot be found.
function(check_python_module module)
  execute_process(
    COMMAND
    ${PYTHON_EXECUTABLE} -c "import ${module}"
    RESULT_VARIABLE
      RET_MODULE_TEST
    ERROR_QUIET
  )
  set(module_name ${ARGN})
  if(NOT module_name)
    set(module_name ${module})
  endif()

  if(RET_MODULE_TEST)
    message(FATAL_ERROR
        "Could not find module ${module_name} for Python "
        "version ${PYTHON_VERSION_MAJOR}.${PYTHON_VERSION_MINOR}. "
        "Make sure to install ${module_name} for this Python version "
        "via \n`${PYTHON_EXECUTABLE} -m pip install ${module_name}'.\n"
        "Note: You need to have pip installed for this Python version.")
  endif()
endfunction()


# Check that scikit-build is installed
# Provides CMake files for Python bindings
# and used to find correct Python includes
# and libraries
check_python_module("skbuild" "scikit-build")

# Find cmake modules distributed with scikit-build
# They are distributed under <scikit-build directory>/resources/cmake
execute_process(
  COMMAND
    ${PYTHON_EXECUTABLE} -c "from __future__ import print_function; \
      import os; import skbuild; \
      cmake_module_path=os.path.join(os.path.dirname(skbuild.__file__), \
        'resources', 'cmake'); print(cmake_module_path, end='')"
  OUTPUT_VARIABLE
    SKBUILD_CMAKE_MODULE_PATH
  RESULT_VARIABLE
    RET_SKBUILD_CMAKE_MODULE_PATH
)

if (NOT EXISTS ${SKBUILD_CMAKE_MODULE_PATH})
  message(FATAL_ERROR "Expected CMake module path from
                       scikit-build at ${SKBUILD_CMAKE_MODULE_PATH}")
endif()

# Add scikit-build cmake files to cmake module path
# Required for Cython target below
list(APPEND CMAKE_MODULE_PATH ${SKBUILD_CMAKE_MODULE_PATH})

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
