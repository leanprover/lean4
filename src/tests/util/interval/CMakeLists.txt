add_executable(interval_tst interval.cpp $<TARGET_OBJECTS:util> $<TARGET_OBJECTS:numerics> $<TARGET_OBJECTS:interval>)
target_link_libraries(interval_tst ${EXTRA_LIBS})
add_test(basic_interval "${CMAKE_CURRENT_BINARY_DIR}/interval_tst")

add_executable(float_interval_tst float_interval.cpp $<TARGET_OBJECTS:util> $<TARGET_OBJECTS:numerics> $<TARGET_OBJECTS:interval>)
target_link_libraries(float_interval_tst ${EXTRA_LIBS})
add_test(float_interval "${CMAKE_CURRENT_BINARY_DIR}/float_interval_tst")

add_executable(double_interval_tst double_interval.cpp $<TARGET_OBJECTS:util> $<TARGET_OBJECTS:numerics> $<TARGET_OBJECTS:interval>)
target_link_libraries(double_interval_tst ${EXTRA_LIBS})
add_test(double_interval "${CMAKE_CURRENT_BINARY_DIR}/double_interval_tst")

add_executable(mpfp_interval_tst mpfp_interval.cpp $<TARGET_OBJECTS:util> $<TARGET_OBJECTS:numerics> $<TARGET_OBJECTS:interval>)
target_link_libraries(mpfp_interval_tst ${EXTRA_LIBS})
add_test(mpfp_interval "${CMAKE_CURRENT_BINARY_DIR}/mpfp_interval_tst")
