# Find GMP
# GMP_FOUND - system has GMP lib
# GMP_INCLUDE_DIR - the GMP include directory
# GMP_LIBRARIES - Libraries needed to use GMP

find_path(GMP_INCLUDE_DIR NAMES gmp.h gmpxx.h)
find_library(GMP_LIBRARIES NAMES gmp)
find_library(GMPXX_LIBRARIES NAMES gmpxx)

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP DEFAULT_MSG GMP_INCLUDE_DIR GMP_LIBRARIES)

mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARIES)
if(GMP_LIBRARIES)
  message(STATUS "Found GMP libs: ${GMP_LIBRARIES}")
endif()
if (GMPXX_LIBRARIES)
  message(STATUS "Found GMPXX libs: ${GMPXX_LIBRARIES}")
endif()
