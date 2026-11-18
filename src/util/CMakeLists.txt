configure_file(ffi.cpp "${CMAKE_BINARY_DIR}/util/ffi.cpp" @ONLY)

add_library(
  util
  OBJECT
  name.cpp
  escaped.cpp
  init_module.cpp
  timeit.cpp
  name_generator.cpp
  kvmap.cpp
  options.cpp
  option_declarations.cpp
  "${CMAKE_BINARY_DIR}/util/ffi.cpp"
)
