set(RUNTIME_OBJS debug.cpp thread.cpp mpz.cpp utf8.cpp
object.cpp apply.cpp exception.cpp interrupt.cpp memory.cpp
stackinfo.cpp compact.cpp init_module.cpp io.cpp hash.cpp
platform.cpp alloc.cpp allocprof.cpp sharecommon.cpp stack_overflow.cpp
process.cpp object_ref.cpp mpn.cpp mutex.cpp libuv.cpp uv/net_addr.cpp uv/event_loop.cpp
uv/timer.cpp uv/tcp.cpp uv/udp.cpp)
if (USE_MIMALLOC)
  list(APPEND RUNTIME_OBJS ${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/src/static.c)
  # Lean code includes it as `lean/mimalloc.h` but for compiling `static.c` itself, add original dir
  include_directories(${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/include)
  set_source_files_properties(${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/src/static.c PROPERTIES
    # (C flags are incomplete, compile as C++ instead like everything else)
    LANGUAGE CXX
    # make all symbols visible, always build with optimizations as otherwise Lean becomes too slow
    COMPILE_FLAGS "-DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -O3 -DNDEBUG -DMI_WIN_NOREDIRECT")
endif()

add_library(leanrt_initial-exec STATIC ${RUNTIME_OBJS})
set_target_properties(leanrt_initial-exec PROPERTIES
  ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})

# The above library, like all other C++ code, is built using `-ftls-model=initial-exec`, which is necessary for linking it into `leanshared`,
# but introduces a measurable overhead while accessing the thread-local variable `g_heap` when allocating and deallocating. Therefore we compile
# the runtime again with the more restrictive `local-exec` and use it when linking Lean code statically, i.e. not against `leanshared`.
add_library(leanrt STATIC ${RUNTIME_OBJS})
set_target_properties(leanrt PROPERTIES
  ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY})
if (NOT MSVC)
target_compile_options(leanrt PRIVATE -ftls-model=local-exec)
endif()
# We do not export Lean symbols when statically linking on Windows.
if(${CMAKE_SYSTEM_NAME} MATCHES "Windows")
target_compile_options(leanrt PRIVATE -ULEAN_EXPORTING)
endif()

if(LLVM)
  if (NOT (CMAKE_CXX_COMPILER_ID MATCHES "Clang"))
      message(FATAL_ERROR "building 'lean.h.bc', need CMAKE_CXX_COMPILER_ID to match Clang to build LLVM bitcode file of Lean runtime.")
  endif()
  FILE(READ "${CMAKE_CURRENT_SOURCE_DIR}/../include/lean/lean.h" LEAN_H)
  # generate LLVM IR for `static inline` definitions in lean.h for the LLVM backend
  string(REPLACE "static inline" "__attribute__((always_inline))" LEAN_H "${LEAN_H}")
  # drop '#pragma once' in .c file to avoid warning
  string(REPLACE "#pragma once" "" LEAN_H "${LEAN_H}")
  file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c" "${LEAN_H}")
  message("Generating LLVM bitcode file for Lean runtime at '${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/lean.h.bc'")
  add_custom_command(
    OUTPUT ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc
    DEPENDS ${RUNTIME_OBJS} ${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c
    COMMAND bash -ec "${CMAKE_BINARY_DIR}/leanc.sh ${LEANC_OPTS} -I$<JOIN:$<TARGET_PROPERTY:leanrt_initial-exec,INCLUDE_DIRECTORIES>, -I> -c ${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c -emit-llvm -o ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc"
    VERBATIM)
  add_custom_target(runtime_bc DEPENDS ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc)
endif()
