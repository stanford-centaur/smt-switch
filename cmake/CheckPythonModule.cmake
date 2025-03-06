# CheckPythonModule.cmake
# A module for checking Python modules with optional version requirements
#
# Usage:
#   # With version requirement
#   check_python_module(Cython 3.0.0)
#   # Without version requirement
#   check_python_module(numpy)
#   # With custom error message
#   check_python_module(Cython 3.0.0 "Cython is required for code generation")
#
# Variables set:
#   PythonModule_${module}_FOUND       - True if the module was found
#   PythonModule_${module}_VERSION     - Module version if available
#   PythonModule_${module}_PATH        - Module path if available

# Make sure Python was found
if(NOT Python_EXECUTABLE)
  find_package(Python COMPONENTS Interpreter REQUIRED)
endif()

function(check_python_module module)
    # Parse arguments
    set(options "")
    set(oneValueArgs "")
    set(multiValueArgs "")
    cmake_parse_arguments(ARG "${options}" "${oneValueArgs}" "${multiValueArgs}" ${ARGN})
    
    # Check if we have a minimum version requirement (first unparsed argument)
    list(LENGTH ARG_UNPARSED_ARGUMENTS arg_count)
    set(min_version "")
    set(custom_error_message "")
    
    if(arg_count GREATER 0)
        list(GET ARG_UNPARSED_ARGUMENTS 0 min_version)
    endif()
    
    # Check if we have a custom error message (second unparsed argument)
    if(arg_count GREATER 1)
        list(GET ARG_UNPARSED_ARGUMENTS 1 custom_error_message)
    endif()
    
    message(STATUS "Checking for Python module ${module}...")
    
    # Check if the module can be imported
    execute_process(
        COMMAND
            ${Python_EXECUTABLE} -c "import ${module}"
        RESULT_VARIABLE
            _${module}_status
        ERROR_VARIABLE
            _${module}_error
        ERROR_STRIP_TRAILING_WHITESPACE
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    
    # If we can't import the module, fail with appropriate error message
    if(NOT _${module}_status EQUAL 0)
        set(PythonModule_${module}_FOUND FALSE PARENT_SCOPE)
        
        if(custom_error_message)
            message(FATAL_ERROR "${custom_error_message}")
        else()
            message(FATAL_ERROR 
                "Required Python module '${module}' not found.\n"
                "Please install it with: ${Python_EXECUTABLE} -m pip install ${module}")
        endif()
        return()
    endif()
    
    # Module was found, now check version if requested
    set(PythonModule_${module}_FOUND TRUE PARENT_SCOPE)
    
    # Try to get the module version
    execute_process(
        COMMAND
            ${Python_EXECUTABLE} -c "import ${module}; print(${module}.__version__ if hasattr(${module}, '__version__') else '')"
        RESULT_VARIABLE
            _${module}_version_status
        OUTPUT_VARIABLE
            _${module}_version
        ERROR_VARIABLE
            _${module}_version_error
        ERROR_STRIP_TRAILING_WHITESPACE
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    
    if(_${module}_version_status EQUAL 0 AND _${module}_version)
        set(PythonModule_${module}_VERSION ${_${module}_version} PARENT_SCOPE)
        
        # Compare version if minimum version is specified
        if(min_version)
            # The Python script returns:
            #  - exit code 0 (success) if the version is sufficient
            #  - exit code 1 (failure) if the version is insufficient
            execute_process(
                COMMAND
                    ${Python_EXECUTABLE} -c "import packaging.version; exit(0 if packaging.version.parse('${_${module}_version}') >= packaging.version.parse('${min_version}') else 1)"
                RESULT_VARIABLE
                    _${module}_min_version_check
                ERROR_VARIABLE
                    _${module}_min_version_error
                ERROR_STRIP_TRAILING_WHITESPACE
            )
            
            # Check the exit code
            if(NOT _${module}_min_version_check EQUAL 0)
                # Version check failed - version is too low
                set(PythonModule_${module}_FOUND FALSE PARENT_SCOPE)
                
                if(custom_error_message)
                    message(FATAL_ERROR "${custom_error_message}")
                else()
                    message(FATAL_ERROR 
                        "Python module ${module} found (version ${_${module}_version}), but version >= ${min_version} is required.\n"
                        "Please upgrade with: ${Python_EXECUTABLE} -m pip install --upgrade \"${module}>=${min_version}\"")
                endif()
            else()
                # Version check succeeded - version is sufficient
                message(STATUS "Found ${module} version ${_${module}_version} (required: >= ${min_version})")
            endif()
        else()
            message(STATUS "Found ${module} version ${_${module}_version}")
        endif()
    else()
        message(STATUS "Found ${module} (version unknown)")
    endif()
    
    # Try to get the module path
    execute_process(
        COMMAND
            ${Python_EXECUTABLE} -c "import ${module}, os; print(os.path.dirname(${module}.__file__) if hasattr(${module}, '__file__') else '')"
        RESULT_VARIABLE
            _${module}_path_status
        OUTPUT_VARIABLE
            _${module}_path
        ERROR_VARIABLE
            _${module}_path_error
        ERROR_STRIP_TRAILING_WHITESPACE
        OUTPUT_STRIP_TRAILING_WHITESPACE
    )
    
    if(_${module}_path_status EQUAL 0 AND _${module}_path)
        set(PythonModule_${module}_PATH ${_${module}_path} PARENT_SCOPE)
    endif()
endfunction()
