add_library(leanlua register_modules.cpp)

target_link_libraries(leanlua ${LEAN_LIBS})
