add_library(leanlua leanlua_state.cpp frontend_lean.cpp)

target_link_libraries(leanlua ${LEAN_LIBS})
