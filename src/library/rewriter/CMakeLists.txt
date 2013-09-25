add_library(rewriter rewriter.cpp fo_match.cpp)
target_link_libraries(rewriter ${LEAN_LIBS})
