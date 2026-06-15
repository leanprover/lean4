# Optional target for building the in-tree Zig runtime library.
# The Zig runtime is additive and not required for the C++ backend.
find_program(ZIG zig)

if(LEAN_ZIG_RUNTIME AND NOT ZIG)
  message(FATAL_ERROR "LEAN_ZIG_RUNTIME=ON requires zig on PATH")
endif()

if(ZIG)
  set(LEAN_ZIG_RUNTIME_PREFIX "${CMAKE_CURRENT_BINARY_DIR}/zig-out")
  set(LEAN_ZIG_RUNTIME_CACHE_DIR "${CMAKE_CURRENT_BINARY_DIR}/.zig-cache")
  set(LEAN_ZIG_RUNTIME_GLOBAL_CACHE_DIR "${CMAKE_CURRENT_BINARY_DIR}/.zig-global-cache")
  set(LEAN_ZIG_RUNTIME_LIB "${LEAN_ZIG_RUNTIME_PREFIX}/lib/libleanrt_zig.a")
  set(LEAN_ZIG_RUNTIME_ALL)
  if(LEAN_ZIG_RUNTIME)
    set(LEAN_ZIG_RUNTIME_ALL ALL)
  endif()

  add_custom_target(
    leanrt_zig ${LEAN_ZIG_RUNTIME_ALL}
    COMMAND "${ZIG}" build --prefix "${LEAN_ZIG_RUNTIME_PREFIX}" --cache-dir "${LEAN_ZIG_RUNTIME_CACHE_DIR}" --global-cache-dir "${LEAN_ZIG_RUNTIME_GLOBAL_CACHE_DIR}"
    BYPRODUCTS "${LEAN_ZIG_RUNTIME_LIB}"
    WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
    COMMENT "Building Lean Zig runtime library"
  )

  if(LEAN_ZIG_RUNTIME)
    add_custom_target(
      leanrt_zig_test
      COMMAND "${ZIG}" build test --test-timeout 60s --prefix "${LEAN_ZIG_RUNTIME_PREFIX}" --cache-dir "${LEAN_ZIG_RUNTIME_CACHE_DIR}" --global-cache-dir "${LEAN_ZIG_RUNTIME_GLOBAL_CACHE_DIR}"
      DEPENDS leanrt_zig
      WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
      COMMENT "Testing Lean Zig runtime library"
    )
  endif()
endif()
