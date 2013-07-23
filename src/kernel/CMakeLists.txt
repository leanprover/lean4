add_library(kernel expr.cpp expr_max_shared)
target_link_libraries(kernel ${EXTRA_LIBS})
