# File: FindPythonVirtualEnv.cmake
# Purpose: Detect and prefer Python from a virtual environment

# Use include guard to prevent multiple inclusions
include_guard(GLOBAL)

# Function to detect and set Python from virtual environment
function(find_python_in_virtualenv)
    # Debugging: Print initial environment information
    message(STATUS "Detecting Python Virtual Environment...")

    # List to store potential Python paths
    set(VENV_PATHS)

    # 1. Standard virtualenv/venv path
    if(DEFINED ENV{VIRTUAL_ENV})
        list(APPEND VENV_PATHS "$ENV{VIRTUAL_ENV}/bin/python")
        message(STATUS "Detected VIRTUAL_ENV: $ENV{VIRTUAL_ENV}")
    endif()

    # 2. Conda environment path
    if(DEFINED ENV{CONDA_PREFIX})
        list(APPEND VENV_PATHS "$ENV{CONDA_PREFIX}/bin/python")
        message(STATUS "Detected CONDA_PREFIX: $ENV{CONDA_PREFIX}")
    endif()

    # Iterate through potential paths to find a valid Python interpreter
    foreach(POTENTIAL_PYTHON IN LISTS VENV_PATHS)
        if(EXISTS "${POTENTIAL_PYTHON}")
            # Verify Python version
            execute_process(
                COMMAND "${POTENTIAL_PYTHON}" -c "import sys; print(f'{sys.version_info.major}.{sys.version_info.minor}')"
                OUTPUT_VARIABLE PYTHON_VERSION
                OUTPUT_STRIP_TRAILING_WHITESPACE
                RESULT_VARIABLE PYTHON_VERSION_RESULT
            )

            if(PYTHON_VERSION_RESULT EQUAL 0)
                # Check if version meets minimum requirements
                if(PYTHON_VERSION VERSION_GREATER_EQUAL "3.9")
                    message(STATUS "Found Virtual Environment Python: ${POTENTIAL_PYTHON}")
                    message(STATUS "Virtual Environment Python Version: ${PYTHON_VERSION}")

                    # Set variables for CMake to use
                    set(Python_EXECUTABLE "${POTENTIAL_PYTHON}" PARENT_SCOPE)
                    set(PYTHON_EXECUTABLE "${POTENTIAL_PYTHON}" PARENT_SCOPE)
                    return()
                endif()
            endif()
        endif()
    endforeach()

    # If no suitable virtual environment Python found, log a message
    message(STATUS "No suitable Python virtual environment found")
endfunction()

