add_library(arithlib nat.cpp int.cpp real.cpp arith.cpp)
target_link_libraries(arithlib ${LEAN_LIBS})
