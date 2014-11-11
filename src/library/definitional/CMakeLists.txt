add_library(definitional rec_on.cpp induction_on.cpp cases_on.cpp
  no_confusion.cpp util.cpp projection.cpp brec_on.cpp)

target_link_libraries(definitional ${LEAN_LIBS})
