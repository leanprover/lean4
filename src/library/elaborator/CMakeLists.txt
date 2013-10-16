add_library(elaborator elaborator.cpp elaborator_trace.cpp)
target_link_libraries(elaborator ${LEAN_LIBS})
