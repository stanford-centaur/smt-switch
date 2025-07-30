# First, ensure we have Python 3.9 or newer with all required components
# Check for a virtualenv python first
find_python_in_virtualenv()
# Want python for building a module, so use Development.Module. See:
# https://stackoverflow.com/questions/78495429/attempting-to-build-python-binary-modules-on-manylinux-find-packagepython3-on
find_package(Python 3.9 REQUIRED COMPONENTS Interpreter Development.Module)

# Include helper function to check for required Python packages
include(CheckPythonModule)

# Verify required Python packages are installed
check_python_module("packaging")

configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/gen-smt-solver-declarations.py"
    "${CMAKE_CURRENT_BINARY_DIR}/gen-smt-solver-declarations.py"
    COPYONLY
)

# Configure setup.py with the correct paths and options
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in"
    "${CMAKE_CURRENT_BINARY_DIR}/setup.py"
    @ONLY  # Use @VAR@ instead of ${VAR} syntax in setup.py.in
)

# Copy pyproject.toml to build directory
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/pyproject.toml"
    "${CMAKE_CURRENT_BINARY_DIR}/pyproject.toml"
    COPYONLY
)

# Add Python package directory containing Cython files.
add_subdirectory(smt_switch)

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

# Collect option flags for generating the smt solvers Cython file
# It will include all of the solvers that are enabled for this build
include_directories(${CMAKE_CURRENT_LIST_DIR})     # For generated files
set(GEN_OPTIONS --dest-dir "${CMAKE_CURRENT_BINARY_DIR}/smt_switch")

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
    "Generate smt_solvers.{pxd,pyx}"
  )

# Custom target for building Python bindings
add_custom_target(python_bindings ALL
    # First ensure the build directory is clean
    COMMAND ${CMAKE_COMMAND} -E remove_directory build
    # Then build the package in place
    COMMAND ${Python_EXECUTABLE} -m pip wheel --no-deps .
    WORKING_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR}
    DEPENDS smt-switch ${SOLVER_BACKEND_LIBS}
    COMMENT "Building Python bindings"
)
add_dependencies(python_bindings gen-smt-solver-declarations)
