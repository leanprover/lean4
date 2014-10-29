add_library(definitional rec_on.cpp induction_on.cpp cases_on.cpp unit.cpp projection.cpp)

target_link_libraries(definitional ${LEAN_LIBS})
