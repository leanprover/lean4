add_executable(shared_test shared.cpp)
target_link_libraries(shared_test ${EXTRA_LIBS} leanshared)
add_test(NAME shared_test
         WORKING_DIRECTORY "${LEAN_BINARY_DIR}"
         COMMAND "${CMAKE_CURRENT_BINARY_DIR}/shared_test")

add_executable(c_name_test name.c)
target_link_libraries(c_name_test ${EXTRA_LIBS} leanshared)
add_test(NAME c_name_test
         WORKING_DIRECTORY "${LEAN_BINARY_DIR}"
         COMMAND "${CMAKE_CURRENT_BINARY_DIR}/c_name_test")

add_executable(c_options_test options.c)
target_link_libraries(c_options_test ${EXTRA_LIBS} leanshared)
add_test(OPTIONS c_options_test
         WORKING_DIRECTORY "${LEAN_BINARY_DIR}"
         COMMAND "${CMAKE_CURRENT_BINARY_DIR}/c_options_test")

add_executable(c_univ_test univ.c)
target_link_libraries(c_univ_test ${EXTRA_LIBS} leanshared)
add_test(UNIV c_univ_test
         WORKING_DIRECTORY "${LEAN_BINARY_DIR}"
         COMMAND "${CMAKE_CURRENT_BINARY_DIR}/c_univ_test")

add_executable(c_expr_test expr.c)
target_link_libraries(c_expr_test ${EXTRA_LIBS} leanshared)
add_test(EXPR c_expr_test
         WORKING_DIRECTORY "${LEAN_BINARY_DIR}"
         COMMAND "${CMAKE_CURRENT_BINARY_DIR}/c_expr_test")
