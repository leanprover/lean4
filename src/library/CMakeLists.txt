add_library(library basic_thms.cpp deep_copy.cpp max_sharing.cpp toplevel.cpp printer.cpp
  formatter.cpp context_to_lambda.cpp state.cpp beta.cpp metavar_env.cpp)
target_link_libraries(library ${LEAN_LIBS})
