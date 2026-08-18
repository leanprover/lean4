if(GMP_INCLUDE_DIR AND GMP_LIBRARIES)
  # Already in cache, be silent
  set(GMP_FIND_QUIETLY TRUE)
endif(GMP_INCLUDE_DIR AND GMP_LIBRARIES)

find_path(GMP_INCLUDE_DIR NAMES gmp.h)
find_library(GMP_LIBRARIES NAMES gmp libgmp mpir)
#find_library(GMPXX_LIBRARIES NAMES gmpxx libgmpxx )
#MESSAGE(STATUS "GMP: " ${GMP_LIBRARIES}) # " " ${GMPXX_LIBRARIES} )

# Extract the version from gmp.h. mpir does not define these macros, so
# GMP_VERSION is left unset there; callers treat an unknown version as not
# satisfying the requirement.
if(GMP_INCLUDE_DIR AND EXISTS "${GMP_INCLUDE_DIR}/gmp.h")
  file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" _gmp_version_major_line REGEX "^#define[ \t]+__GNU_MP_VERSION[ \t]+[0-9]+")
  file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" _gmp_version_minor_line REGEX "^#define[ \t]+__GNU_MP_VERSION_MINOR[ \t]+[0-9]+")
  file(STRINGS "${GMP_INCLUDE_DIR}/gmp.h" _gmp_version_patch_line REGEX "^#define[ \t]+__GNU_MP_VERSION_PATCHLEVEL[ \t]+[0-9]+")
  if(_gmp_version_major_line AND _gmp_version_minor_line AND _gmp_version_patch_line)
    string(REGEX REPLACE "^#define[ \t]+__GNU_MP_VERSION[ \t]+([0-9]+).*" "\\1" _gmp_version_major "${_gmp_version_major_line}")
    string(REGEX REPLACE "^#define[ \t]+__GNU_MP_VERSION_MINOR[ \t]+([0-9]+).*" "\\1" _gmp_version_minor "${_gmp_version_minor_line}")
    string(REGEX REPLACE "^#define[ \t]+__GNU_MP_VERSION_PATCHLEVEL[ \t]+([0-9]+).*" "\\1" _gmp_version_patch "${_gmp_version_patch_line}")
    set(GMP_VERSION "${_gmp_version_major}.${_gmp_version_minor}.${_gmp_version_patch}")
  endif()
  unset(_gmp_version_major_line)
  unset(_gmp_version_minor_line)
  unset(_gmp_version_patch_line)
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(GMP
  REQUIRED_VARS GMP_INCLUDE_DIR GMP_LIBRARIES
  VERSION_VAR GMP_VERSION)
mark_as_advanced(GMP_INCLUDE_DIR GMP_LIBRARIES)
