# First, ensure we have Python 3.9 or newer with all required components
# Check for a virtualenv python first
find_package(PythonVirtualEnv)
# Want python for building a module, so use Development.Module. See:
# https://stackoverflow.com/questions/78495429/attempting-to-build-python-binary-modules-on-manylinux-find-packagepython3-on
find_package(Python 3.9 REQUIRED COMPONENTS Interpreter Development.Module)

# Helper function to check for required Python packages
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

# Verify required Python packages are installed
check_python_module("setuptools")
check_python_module("wheel")
check_python_module("cython" "Cython>=3.0.0")

# Set up the Python package directory structure
set(PYTHON_PACKAGE_DIR "${CMAKE_CURRENT_BINARY_DIR}/smt_switch")
file(MAKE_DIRECTORY ${PYTHON_PACKAGE_DIR})

configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/gen-smt-solver-declarations.py"
    "${CMAKE_CURRENT_BINARY_DIR}/gen-smt-solver-declarations.py"
    COPYONLY
)

# Copy necessary Cython source files to the build directory
file(GLOB CYTHON_SOURCE_FILES
    "${CMAKE_CURRENT_SOURCE_DIR}/*.pyx"
    "${CMAKE_CURRENT_SOURCE_DIR}/*.pxd"
    "${CMAKE_CURRENT_SOURCE_DIR}/*.pxi"
)

# Cache the list of files
set(CYTHON_SOURCE_FILES ${CYTHON_SOURCE_FILES} CACHE INTERNAL "")

# Force CMake to rerun if any of these files change
foreach(CYTHON_FILE ${CYTHON_SOURCE_FILES})
    get_filename_component(FILE_NAME "${CYTHON_FILE}" NAME)
    configure_file(
        ${CYTHON_FILE}
        "${CMAKE_CURRENT_BINARY_DIR}/${FILE_NAME}"
        COPYONLY
    )
endforeach()

# Configure setup.py with the correct paths and options
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in"
    "${CMAKE_CURRENT_BINARY_DIR}/setup.py"
    @ONLY  # Use @VAR@ instead of ${VAR} syntax in setup.py.in
)

file(MAKE_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}/smt_switch)
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/__init__.py.in"
    "${CMAKE_CURRENT_BINARY_DIR}/smt_switch/__init__.py"
    @ONLY
)
file(COPY "${CMAKE_CURRENT_SOURCE_DIR}/pysmt_frontend"
     DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/smt_switch/")

# Copy pyproject.toml to build directory
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/pyproject.toml"
    "${CMAKE_CURRENT_BINARY_DIR}/pyproject.toml"
    COPYONLY
)

# Handle macOS-specific configuration
if(APPLE)
    # Detect architecture for proper compilation flags
    execute_process(
        COMMAND uname -m
        OUTPUT_VARIABLE MACOS_ARCH
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    set(MACOS_ARCH ${MACOS_ARCH} CACHE STRING "macOS architecture")
endif()

# generate necessary collateral here
include_directories(${CMAKE_CURRENT_LIST_DIR})     # For generated files
set(GEN_OPTIONS --dest-dir ${CMAKE_CURRENT_BINARY_DIR})

if (BUILD_BTOR)
  set(GEN_OPTIONS ${GEN_OPTIONS} --btor)
endif()

if (BUILD_BITWUZLA)
  set(GEN_OPTIONS ${GEN_OPTIONS} --bitwuzla)
endif()

if (BUILD_CVC5)
  set(GEN_OPTIONS ${GEN_OPTIONS} --cvc5)
endif()

if (BUILD_MSAT)
  set(GEN_OPTIONS ${GEN_OPTIONS} --msat)
endif()

if (BUILD_YICES2)
  set(GEN_OPTIONS ${GEN_OPTIONS} --yices2)
endif()

if (BUILD_Z3)
  set(GEN_OPTIONS ${GEN_OPTIONS} --z3)
endif()

# Add custom target for building Python bindings
add_custom_target(python_bindings ALL
    # First ensure the build directory is clean
    COMMAND ${CMAKE_COMMAND} -E remove_directory build
    # Then build the package in place
    COMMAND ${Python_EXECUTABLE} -m pip install --no-deps -e .
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    DEPENDS smt-switch  # Main library target
    COMMENT "Building Python bindings"
)

message(STATUS "Running gen-smt-solver-declarations.py ${GEN_OPTIONS}")
add_custom_target(gen-smt-solver-declarations
  ALL
  COMMAND
    ${PYTHON_EXECUTABLE}
    ${CMAKE_CURRENT_BINARY_DIR}/gen-smt-solver-declarations.py
    ${GEN_OPTIONS}
  DEPENDS
    gen-smt-solver-declarations.py
  COMMENT
    "Generate smt_solvers.{pxd,pxi}"
  )
add_dependencies(python_bindings gen-smt-solver-declarations)

# Add install target for Python package
install(CODE
    "execute_process(COMMAND ${Python_EXECUTABLE} -m pip install --no-deps . \
     WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})"
    COMPONENT python
)
