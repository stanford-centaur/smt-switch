# Configure __init__.py
configure_file(
    "${CMAKE_CURRENT_SOURCE_DIR}/__init__.py.in"
    "${CMAKE_CURRENT_BINARY_DIR}/__init__.py"
    @ONLY
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

# Copy PySmt frontend subpackage.
file(COPY "${CMAKE_CURRENT_SOURCE_DIR}/pysmt_frontend"
     DESTINATION "${CMAKE_CURRENT_BINARY_DIR}/")
