configure_file(ffi.cpp "${CMAKE_BINARY_DIR}/util/ffi.cpp" @ONLY)

add_library(util OBJECT name.cpp name_set.cpp
  escaped.cpp bit_tricks.cpp ascii.cpp
  path.cpp lbool.cpp init_module.cpp list_fn.cpp
  timeit.cpp timer.cpp
  name_generator.cpp kvmap.cpp map_foreach.cpp
  options.cpp option_declarations.cpp
  "${CMAKE_BINARY_DIR}/util/ffi.cpp")
