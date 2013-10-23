add_library(elaborator elaborator.cpp elaborator_justification.cpp)
target_link_libraries(elaborator ${LEAN_LIBS})
