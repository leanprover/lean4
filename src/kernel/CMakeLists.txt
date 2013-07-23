add_library(kernel expr.cpp max_sharing.cpp free_vars.cpp)
target_link_libraries(kernel ${EXTRA_LIBS})
