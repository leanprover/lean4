add_library(native_compiler OBJECT init_module.cpp native_compiler.cpp
  cpp_emitter.cpp options.cpp used_defs.cpp cpp_compiler.cpp extern.cpp)
