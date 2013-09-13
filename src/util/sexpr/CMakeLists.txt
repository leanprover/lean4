add_library(sexpr sexpr.cpp sexpr_fn.cpp format.cpp options.cpp)
target_link_libraries(sexpr ${LEAN_LIBS})
