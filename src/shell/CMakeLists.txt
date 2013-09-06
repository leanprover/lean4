configure_file("${LEAN_SOURCE_DIR}/shell/version.h.in" "${LEAN_BINARY_DIR}/version.h")
include_directories("${LEAN_BINARY_DIR}")
add_executable(lean lean.cpp)
target_link_libraries(lean ${EXTRA_LIBS})
add_test(example1 ${CMAKE_CURRENT_BINARY_DIR}/lean "${LEAN_SOURCE_DIR}/../examples/lean/ex1.lean")
add_test(example2 ${CMAKE_CURRENT_BINARY_DIR}/lean "${LEAN_SOURCE_DIR}/../examples/lean/ex2.lean")
add_test(example3 ${CMAKE_CURRENT_BINARY_DIR}/lean "${LEAN_SOURCE_DIR}/../examples/lean/ex3.lean")
add_test(NAME leantests
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean"
         COMMAND "./test.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
add_test(NAME leanslowtests
         WORKING_DIRECTORY "${LEAN_SOURCE_DIR}/../tests/lean/slow"
         COMMAND "../test.sh" "${CMAKE_CURRENT_BINARY_DIR}/lean")
