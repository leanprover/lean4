add_executable(shell_test shell.cpp)
target_link_libraries(shell_test "init" "lean_frontend" "library" "kernel" "util" "shell" ${EXTRA_LIBS})

add_test(NAME "emscripten_test"
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/tests/shell"
         COMMAND bash "${LEAN_SOURCE_DIR}/tests/shell/test.sh" "${CMAKE_CURRENT_BINARY_DIR}/shell_test")
