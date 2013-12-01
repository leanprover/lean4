add_library(util trace.cpp debug.cpp name.cpp name_set.cpp
  exception.cpp interrupt.cpp hash.cpp escaped.cpp bit_tricks.cpp
  safe_arith.cpp ascii.cpp memory.cpp shared_mutex.cpp realpath.cpp
  script_state.cpp script_exception.cpp splay_map.cpp lua.cpp
  luaref.cpp stackinfo.cpp)

target_link_libraries(util ${LEAN_LIBS})
