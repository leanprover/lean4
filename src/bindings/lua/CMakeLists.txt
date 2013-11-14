add_library(lua util.cpp lua_exception.cpp name.cpp numerics.cpp
lref.cpp splay_map.cpp options.cpp sexpr.cpp format.cpp level.cpp
local_context.cpp expr.cpp context.cpp object.cpp environment.cpp
formatter.cpp state.cpp leanlua_state.cpp)

target_link_libraries(lua ${LEAN_LIBS})
