add_library(definitional rec_on.cpp induction_on.cpp cases_on.cpp unit.cpp eq.cpp heq.cpp
  no_confusion.cpp util.cpp projection.cpp)

target_link_libraries(definitional ${LEAN_LIBS})
