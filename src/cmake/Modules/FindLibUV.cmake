if(LIBUV_FOUND)
  # Already in cache, be silent
  set(LIBUV_FIND_QUIETLY TRUE)
endif(LIBUV_FOUND)

find_package(PkgConfig REQUIRED)
pkg_search_module(LIBUV REQUIRED libuv)
message(STATUS "LIBUV_LDFLAGS: " ${LIBUV_LDFLAGS})
message(STATUS "LIBUV_INCLUDE_DIRS: " ${LIBUV_INCLUDE_DIRS})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(LibUV DEFAULT_MSG LIBUV_FOUND)
mark_as_advanced(LIBUV_INCLUDE_DIRS LIBUV_LDFLAGS)
