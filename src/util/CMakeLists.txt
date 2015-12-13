add_library(util OBJECT debug.cpp name.cpp name_set.cpp
  name_generator.cpp exception.cpp interrupt.cpp hash.cpp escaped.cpp
  bit_tricks.cpp safe_arith.cpp ascii.cpp memory.cpp shared_mutex.cpp
  realpath.cpp script_state.cpp script_exception.cpp rb_map.cpp
  lua.cpp luaref.cpp lua_named_param.cpp stackinfo.cpp lean_path.cpp
  serializer.cpp lbool.cpp thread_script_state.cpp bitap_fuzzy_search.cpp
  init_module.cpp thread.cpp memory_pool.cpp utf8.cpp name_map.cpp list_fn.cpp
  null_ostream.cpp file_lock.cpp)
