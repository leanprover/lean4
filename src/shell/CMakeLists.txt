configure_file("${LEAN_SOURCE_DIR}/shell/version.h.in" "${LEAN_BINARY_DIR}/version.h")
include_directories("${LEAN_BINARY_DIR}")
add_executable(lean lean.cpp)
target_link_libraries(lean ${EXTRA_LIBS})
add_test(NAME leantests
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
         COMMAND "./test.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
