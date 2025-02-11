# First, find Python and required packages
find_package(Python 3.9 REQUIRED COMPONENTS Interpreter Development)

# Keep the useful module checking function
function(check_python_module module)
  execute_process(
    COMMAND
    ${Python_EXECUTABLE} -c "import ${module}"
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
        "version ${Python_VERSION_MAJOR}.${Python_VERSION_MINOR}. "
        "Make sure to install ${module_name} for this Python version "
        "via \n`${Python_EXECUTABLE} -m pip install ${module_name}'.\n"
        "Note: You need to have pip installed for this Python version.")
  endif()
endfunction()

# Check for required Python packages
check_python_module("setuptools")
check_python_module("wheel")
check_python_module("cython" "Cython>=3.0.0")

# Find Cython package
find_package(Cython 3.0.0 REQUIRED)

# Set up the Python package directory structure
set(PYTHON_PACKAGE_DIR "${CMAKE_CURRENT_BINARY_DIR}/smt_switch")
file(MAKE_DIRECTORY ${PYTHON_PACKAGE_DIR})

# Add Cython target
add_cython_target(smt_switch CXX)
add_library(smt_switch_module MODULE ${smt_switch})

# Include directories and link libraries
target_include_directories(smt_switch_module PRIVATE
    "${PROJECT_SOURCE_DIR}/include"
    ${CMAKE_CURRENT_LIST_DIR}  # For generated files
)
target_link_libraries(smt_switch_module PRIVATE smt-switch)

# Handle solver-specific configuration
set(GEN_OPTIONS --dest-dir ${CMAKE_CURRENT_LIST_DIR})

if(BUILD_BTOR)
    target_include_directories(smt_switch_module PRIVATE "${PROJECT_SOURCE_DIR}/btor/include")
    target_link_libraries(smt_switch_module PRIVATE smt-switch-btor)
    set(GEN_OPTIONS ${GEN_OPTIONS} --btor)
endif()

if(BUILD_BITWUZLA)
    target_include_directories(smt_switch_module PRIVATE "${PROJECT_SOURCE_DIR}/bitwuzla/include")
    target_link_libraries(smt_switch_module PRIVATE smt-switch-bitwuzla)
    set(GEN_OPTIONS ${GEN_OPTIONS} --bitwuzla)
endif()

if (BUILD_CVC5)
  target_include_directories(smt_switch_module PRIVATE "${PROJECT_SOURCE_DIR}/cvc5/include")
  target_link_libraries(smt_switch_module PRIVATE smt-switch-cvc5)
  set(GEN_OPTIONS ${GEN_OPTIONS} --cvc5)
endif()

if (BUILD_MSAT)
  target_include_directories(smt_switch_module PRIVATE "${PROJECT_SOURCE_DIR}/msat/include")
  target_link_libraries(smt_switch_module PRIVATE smt-switch-msat)
  set(GEN_OPTIONS ${GEN_OPTIONS} --msat)
endif()

if (BUILD_YICES2)
  target_include_directories(smt_switch_module PRIVATE "${PROJECT_SOURCE_DIR}/yices2/include")
  target_link_libraries(smt_switch_module PRIVATE smt-switch-yices2)
  set(GEN_OPTIONS ${GEN_OPTIONS} --yices2)
endif()

if (BUILD_Z3)
  target_include_directories(smt_switch_module PRIVATE "${PROJECT_SOURCE_DIR}/z3/include")
  target_link_libraries(smt_switch_module PRIVATE smt-switch-z3)
  set(GEN_OPTIONS ${GEN_OPTIONS} --z3)
endif()

# Generate solver declarations
add_custom_target(gen-smt-solver-declarations
    ALL
    COMMAND
        ${Python_EXECUTABLE}
        ${CMAKE_CURRENT_LIST_DIR}/gen-smt-solver-declarations.py
        ${GEN_OPTIONS}
    DEPENDS
        gen-smt-solver-declarations.py
    COMMENT
        "Generate smt_solvers.{pxd,pxi}"
)

# Mark as Python extension
python_extension_module(smt_switch_module)
add_dependencies(smt_switch_module gen-smt-solver-declarations)

# Configure setup.py and pyproject.toml
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in"
    "${CMAKE_CURRENT_BINARY_DIR}/setup.py"
    @ONLY
)

configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/pyproject.toml"
    "${CMAKE_CURRENT_BINARY_DIR}/pyproject.toml"
    COPYONLY
)

# Copy initialization files
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/__init__.py.in"
    "${PYTHON_PACKAGE_DIR}/__init__.py"
    COPYONLY
)

# Set up pysmt frontend
file(MAKE_DIRECTORY "${PYTHON_PACKAGE_DIR}/pysmt_frontend")
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/pysmt_frontend/__init__.py"
    "${PYTHON_PACKAGE_DIR}/pysmt_frontend/__init__.py"
    COPYONLY
)
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/pysmt_frontend/pysmt_solver.py"
    "${PYTHON_PACKAGE_DIR}/pysmt_frontend/pysmt_solver.py"
    COPYONLY
)

# Add custom target for building Python package
add_custom_target(python_bindings ALL
    COMMAND ${Python_EXECUTABLE} -m pip install --no-deps -e .
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    DEPENDS smt_switch_module
    COMMENT "Building Python bindings"
)

# Install targets
install(TARGETS smt_switch_module DESTINATION lib)
install(CODE "execute_process(COMMAND ${Python_EXECUTABLE} -m pip install --no-deps . WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})"
        COMPONENT python)
