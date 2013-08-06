add_library(kernel expr.cpp max_sharing.cpp free_vars.cpp abstract.cpp
  instantiate.cpp deep_copy.cpp normalize.cpp level.cpp environment.cpp
  type_check.cpp context.cpp builtin.cpp toplevel.cpp)
target_link_libraries(kernel ${EXTRA_LIBS})
