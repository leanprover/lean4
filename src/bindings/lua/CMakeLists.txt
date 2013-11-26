add_library(lua util.cpp lua_exception.cpp name.cpp numerics.cpp
lref.cpp splay_map.cpp options.cpp sexpr.cpp format.cpp level.cpp
local_context.cpp expr.cpp context.cpp object.cpp environment.cpp
formatter.cpp justification.cpp metavar_env.cpp type_inferer.cpp
io_state.cpp goal.cpp proof_builder.cpp cex_builder.cpp
proof_state.cpp leanlua_state.cpp frontend_lean.cpp)

target_link_libraries(lua ${LEAN_LIBS})
