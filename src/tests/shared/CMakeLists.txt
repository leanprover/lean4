add_executable(shared_test shared.cpp)
target_link_libraries(shared_test ${EXTRA_LIBS} leanshared)
