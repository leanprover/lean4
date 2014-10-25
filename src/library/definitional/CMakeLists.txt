add_library(definitional rec_on.cpp induction_on.cpp)

target_link_libraries(definitional ${LEAN_LIBS})
