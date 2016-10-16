add_executable(shell_test shell.cpp $<TARGET_OBJECTS:shell_js>)
target_link_libraries(shell_test leanstatic)

# TODO(Leo): add after stdlib is activated again
# add_test(NAME "emscripten_test"
#          WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/tests/shell"
#          COMMAND bash "${LEAN_SOURCE_DIR}/tests/shell/test.sh" "${CMAKE_CURRENT_BINARY_DIR}/shell_test")
