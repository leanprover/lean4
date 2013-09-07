add_library(arithlib natlib.cpp intlib.cpp reallib.cpp specialfnlib.cpp arithlibs.cpp)
target_link_libraries(arithlib ${LEAN_LIBS})
