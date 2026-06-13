cmake_minimum_required(VERSION 3.20)

project(leanrt_cpp_partial LANGUAGES CXX)

if(NOT DEFINED LEAN4_DIR)
  # zig-backend/cmake/leanrt_cpp_partial sits three levels below the lean4 root.
  get_filename_component(LEAN4_DIR "${CMAKE_CURRENT_SOURCE_DIR}/../../.." ABSOLUTE)
endif()
set(LEAN4_RUNTIME_DIR "${LEAN4_DIR}/src/runtime")

set(GMP_PREFIX "/opt/homebrew/opt/gmp" CACHE PATH "GMP installation prefix")
set(LIBUV_PREFIX "/opt/homebrew/opt/libuv" CACHE PATH "libuv installation prefix")

set(CMAKE_CXX_STANDARD 20)
set(CMAKE_CXX_STANDARD_REQUIRED ON)
set(CMAKE_CXX_EXTENSIONS OFF)

add_library(
  leanrt_cpp_partial
  STATIC
  thread_partial.cpp
  interrupt_partial.cpp
  object_partial.cpp
  allocator_owner.cpp
  init_module_partial.cpp
  io_partial.cpp
  libuv_partial.cpp
)

target_compile_definitions(
  leanrt_cpp_partial
  PRIVATE
    LEAN_EXPORTING
    LEAN_MULTI_THREAD
    LEAN_MMAP
    LEAN_BUILD_TYPE="Release"
    lean_inc_heartbeat=leanrt_cpp_partial_hidden_lean_inc_heartbeat_impl
    lean_utf8_strlen=leanrt_cpp_partial_hidden_lean_utf8_strlen_impl
    lean_utf8_n_strlen=leanrt_cpp_partial_hidden_lean_utf8_n_strlen_impl
)

target_include_directories(
  leanrt_cpp_partial
  PRIVATE
    "${CMAKE_CURRENT_SOURCE_DIR}/include"
    "${LEAN4_DIR}"
    "${LEAN4_DIR}/src"
    "${LEAN4_DIR}/src/include"
    "${LEAN4_RUNTIME_DIR}"
    "${GMP_PREFIX}/include"
    "${LIBUV_PREFIX}/include"
)

set(LEANRT_OBJECT_PARTIAL_SOURCE "${CMAKE_BINARY_DIR}/object_partial.cpp")
execute_process(
  COMMAND
    python3
    "${CMAKE_CURRENT_SOURCE_DIR}/generate_object_partial.py"
    "${LEAN4_RUNTIME_DIR}/object.cpp"
    "${LEANRT_OBJECT_PARTIAL_SOURCE}"
  COMMAND_ERROR_IS_FATAL ANY
)

target_sources(
  leanrt_cpp_partial
  PRIVATE
    "${LEAN4_RUNTIME_DIR}/debug.cpp"
    "${LEAN4_RUNTIME_DIR}/alloc.cpp"
    "${LEAN4_RUNTIME_DIR}/mpz.cpp"
    "${LEAN4_RUNTIME_DIR}/exception.cpp"
    "${LEAN4_RUNTIME_DIR}/memory.cpp"
    "${LEAN4_RUNTIME_DIR}/stackinfo.cpp"
    "${LEAN4_RUNTIME_DIR}/compact.cpp"
    "${LEAN4_RUNTIME_DIR}/hash.cpp"
    "${LEAN4_RUNTIME_DIR}/utf8.cpp"
    "${LEAN4_RUNTIME_DIR}/byteslice.cpp"
    "${LEAN4_RUNTIME_DIR}/platform.cpp"
    "${LEAN4_RUNTIME_DIR}/allocprof.cpp"
    "${LEAN4_RUNTIME_DIR}/sharecommon.cpp"
    "${LEAN4_RUNTIME_DIR}/stack_overflow.cpp"
    "${LEAN4_RUNTIME_DIR}/process.cpp"
    "${LEAN4_RUNTIME_DIR}/object_ref.cpp"
    "${LEAN4_RUNTIME_DIR}/mpn.cpp"
    "${LEAN4_RUNTIME_DIR}/mutex.cpp"
    "${LEAN4_RUNTIME_DIR}/uv/net_addr.cpp"
    "${LEAN4_RUNTIME_DIR}/uv/event_loop.cpp"
    "${LEAN4_RUNTIME_DIR}/uv/timer.cpp"
    "${LEAN4_RUNTIME_DIR}/uv/tcp.cpp"
    "${LEAN4_RUNTIME_DIR}/uv/udp.cpp"
    "${LEAN4_RUNTIME_DIR}/uv/dns.cpp"
    "${LEAN4_RUNTIME_DIR}/uv/system.cpp"
    "${LEAN4_RUNTIME_DIR}/uv/signal.cpp"
)

set_target_properties(
  leanrt_cpp_partial
  PROPERTIES
    ARCHIVE_OUTPUT_DIRECTORY "${CMAKE_BINARY_DIR}"
    OUTPUT_NAME "leanrt_cpp_partial"
)

target_compile_definitions(
  leanrt_cpp_partial
  PRIVATE
    LEANRT_CPP_PARTIAL_OBJECT_CPP="${LEANRT_OBJECT_PARTIAL_SOURCE}"
)
