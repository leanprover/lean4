add_library(lua util.cpp name.cpp numerics.cpp options.cpp sexpr.cpp format.cpp leanlua_state.cpp)
target_link_libraries(lua ${LEAN_LIBS})

