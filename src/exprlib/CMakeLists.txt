add_library(exprlib basic_thms.cpp deep_copy.cpp max_sharing.cpp toplevel.cpp printer.cpp
  formatter.cpp context_to_lambda.cpp state.cpp)
target_link_libraries(exprlib ${LEAN_LIBS})
