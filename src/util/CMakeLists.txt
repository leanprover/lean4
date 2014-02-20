if (("${BOOST}" MATCHES "ON") AND ("${MULTI_THREAD}" MATCHES "ON"))
  set(THREAD_CPP "thread.cpp")
else()
  set(THREAD_CPP "")
endif()

add_library(util trace.cpp debug.cpp name.cpp name_set.cpp name_generator.cpp
  exception.cpp interrupt.cpp hash.cpp escaped.cpp bit_tricks.cpp
  safe_arith.cpp ascii.cpp memory.cpp shared_mutex.cpp realpath.cpp
  script_state.cpp script_exception.cpp splay_map.cpp lua.cpp
  luaref.cpp stackinfo.cpp lean_path.cpp serializer.cpp ${THREAD_CPP})

target_link_libraries(util ${LEAN_LIBS})
