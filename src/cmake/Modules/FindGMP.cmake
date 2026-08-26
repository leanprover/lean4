if(GMP_INCLUDE_DIR AND GMP_LIBRARIES)
  # Already in cache, be silent
  set(GMP_FIND_QUIETLY TRUE)
endif(GMP_INCLUDE_DIR AND GMP_LIBRARIES)

# `gmp.pc` is the only reliable source for the version: on Fedora and RHEL `gmp.h`
# merely dispatches to an arch-specific header and defines no version macros.
# PkgConfig is not REQUIRED here so that FORCE_GMP still works without it.
find_package(PkgConfig)
if(PKG_CONFIG_FOUND)
  pkg_check_modules(PC_GMP QUIET gmp)
endif()
set(GMP_VERSION "${PC_GMP_VERSION}")

find_path(GMP_INCLUDE_DIR NAMES gmp.h HINTS ${PC_GMP_INCLUDEDIR} ${PC_GMP_INCLUDE_DIRS})
find_library(GMP_LIBRARIES NAMES gmp libgmp HINTS ${PC_GMP_LIBDIR} ${PC_GMP_LIBRARY_DIRS})
#find_library(GMPXX_LIBRARIES NAMES gmpxx libgmpxx )
#MESSAGE(STATUS "GMP: " ${GMP_LIBRARIES}) # " " ${GMPXX_LIBRARIES} )

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP
  REQUIRED_VARS GMP_INCLUDE_DIR GMP_LIBRARIES
  VERSION_VAR GMP_VERSION)
mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARIES)
