add_library(exprlib basic_thms.cpp deep_copy.cpp max_sharing.cpp toplevel.cpp)
target_link_libraries(exprlib ${LEAN_LIBS})
