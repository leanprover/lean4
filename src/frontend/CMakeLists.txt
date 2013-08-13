add_library(frontend frontend.cpp operator_info.cpp scanner.cpp)
target_link_libraries(frontend ${LEAN_LIBS})
