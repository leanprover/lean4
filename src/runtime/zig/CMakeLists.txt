# Optional target for building the in-tree Zig runtime library.
# The Zig runtime is additive and not required for the C++ backend.
find_program(ZIG zig)
if(ZIG)
  add_custom_target(
    leanrt_zig
    COMMAND "${ZIG}" build --prefix "${CMAKE_CURRENT_BINARY_DIR}/zig-out"
    WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
    COMMENT "Building Lean Zig runtime library"
  )
endif()
