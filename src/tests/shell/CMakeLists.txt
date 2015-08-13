add_executable(shell_test shell.cpp ${LEAN_OBJS} $<TARGET_OBJECTS:shell>)
target_link_libraries(shell_test ${EXTRA_LIBS})

add_test(NAME "emscripten_test"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/tests/shell"
         COMMAND bash "${LEAN_SOURCE_DIR}/tests/shell/test.sh" "${CMAKE_CURRENT_BINARY_DIR}/shell_test")
