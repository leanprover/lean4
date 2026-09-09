if(USE_MIMALLOC)
  set(MIMALLOC_SRC ${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/src/static.c)
  # (C flags are incomplete, compile as C++ instead like everything else). A source property rather
  # than a target one, but it is the same for every variant below.
  set_source_files_properties(${MIMALLOC_SRC} PROPERTIES LANGUAGE CXX)
  # Make all symbols visible, always build with optimizations as otherwise Lean becomes too slow.
  # `MI_MAX_ALIGN_SIZE=8` means that an object with two fields will take 24 bytes instead of 32 bytes.
  # The default value 16 is only necessary for mimalloc to be compatible with the system allocator, which
  # we do not care about.
  set(MIMALLOC_OPTS -DMI_SHARED_LIB -DMI_SHARED_LIB_EXPORT -O3 -DNDEBUG -DMI_WIN_NOREDIRECT -DMI_MAX_ALIGN_SIZE=8 -Wno-unused-function)
  if(CMAKE_CXX_COMPILER_ID MATCHES "AppleClang|Clang")
    list(APPEND MIMALLOC_OPTS -Wno-deprecated)
  endif()

  # One target per (mitigation level, TLS model) the build needs, each carrying its own
  # `target_compile_options`. The flags cannot live on the shared source instead: source properties
  # are directory-scoped and CMake emits them *after* target options, so a target trying to override
  # the mitigation level would silently lose to whatever the source property set.
  function(add_mimalloc_variant name type secure)
    add_library(${name} ${type} ${MIMALLOC_SRC})
    # Lean code includes it as `lean/mimalloc.h`, but `static.c` itself wants the original directory
    target_include_directories(${name} PRIVATE ${LEAN_BINARY_DIR}/../mimalloc/src/mimalloc/include)
    target_compile_options(${name} PRIVATE ${MIMALLOC_OPTS} -DMI_SECURE=${secure} ${ARGN})
  endfunction()

  # `local-exec` matches the `leanrt` rationale below: those copies are only ever linked into an
  # executable, never into `leanshared`.
  set(MIMALLOC_LOCAL_EXEC_OPTS "")
  if(NOT MSVC)
    list(APPEND MIMALLOC_LOCAL_EXEC_OPTS -ftls-model=local-exec)
  endif()

  # Level 3 buys encoded free lists, which turn a stale reference-count operation on a freed object
  # into a checked abort rather than silent heap corruption, and the padding it implies, which
  # catches writes past an object. Level 4 adds only a double-free check that reports and continues.
  # a real archive rather than an object library: the link rule refers to it as `-lmimalloc_paranoid`
  add_mimalloc_variant(mimalloc_paranoid STATIC 3 ${MIMALLOC_LOCAL_EXEC_OPTS})
  # only `leanchecker-paranoid` consumes it, and that target is not built by default
  set_target_properties(
    mimalloc_paranoid
    PROPERTIES EXCLUDE_FROM_ALL TRUE ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}
  )
endif()

# Later stages import the previous stage's copies of everything below (see `src/CMakeLists.txt`).
# `mimalloc_paranoid` is not among them, as the previous stage does not build it by default.
if(STAGE GREATER 1)
  return()
endif()

set(
  RUNTIME_OBJS
  debug.cpp
  thread.cpp
  mpz.cpp
  utf8.cpp
  object.cpp
  apply.cpp
  exception.cpp
  interrupt.cpp
  memory.cpp
  stackinfo.cpp
  compact.cpp
  init_module.cpp
  io.cpp
  hash.cpp
  byteslice.cpp
  platform.cpp
  alloc.cpp
  allocprof.cpp
  sharecommon.cpp
  stack_overflow.cpp
  process.cpp
  object_ref.cpp
  mpn.cpp
  mutex.cpp
  libuv.cpp
  uv/net_addr.cpp
  uv/event_loop.cpp
  uv/timer.cpp
  uv/tcp.cpp
  uv/udp.cpp
  uv/dns.cpp
  uv/system.cpp
  uv/signal.cpp
  openssl.cpp
)

add_library(leanrt_initial-exec STATIC ${RUNTIME_OBJS})
set_target_properties(leanrt_initial-exec PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})

# The above library, like all other C++ code, is built using `-ftls-model=initial-exec`, which is necessary for linking it into `leanshared`,
# but introduces a measurable overhead while accessing the thread-local variable `g_heap` when allocating and deallocating. Therefore we compile
# the runtime again with the more restrictive `local-exec` and use it when linking Lean code statically, i.e. not against `leanshared`.
add_library(leanrt STATIC ${RUNTIME_OBJS})
set_target_properties(leanrt PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY})
if(NOT MSVC)
  target_compile_options(leanrt PRIVATE -ftls-model=local-exec)
endif()
# adds each variant's object to the archive; its `PRIVATE` flags do not propagate to the rest
if(USE_MIMALLOC)
  add_mimalloc_variant(mimalloc_initial-exec OBJECT ${LEAN_MI_SECURE})
  add_mimalloc_variant(mimalloc_local-exec OBJECT ${LEAN_MI_SECURE} ${MIMALLOC_LOCAL_EXEC_OPTS})
  target_link_libraries(leanrt_initial-exec PRIVATE mimalloc_initial-exec)
  target_link_libraries(leanrt PRIVATE mimalloc_local-exec)
endif()
# We do not export Lean symbols when statically linking on Windows.
if(CMAKE_SYSTEM_NAME MATCHES "Windows")
  target_compile_options(leanrt PRIVATE -ULEAN_EXPORTING)
endif()

if(LLVM)
  if(NOT CMAKE_CXX_COMPILER_ID MATCHES "Clang")
    message(
      FATAL_ERROR
      "building 'lean.h.bc', need CMAKE_CXX_COMPILER_ID to match Clang to build LLVM bitcode file of Lean runtime."
    )
  endif()
  file(READ "${CMAKE_CURRENT_SOURCE_DIR}/../include/lean/lean.h" LEAN_H)
  # generate LLVM IR for `static inline` definitions in lean.h for the LLVM backend
  string(REPLACE "static inline" "__attribute__((always_inline))" LEAN_H "${LEAN_H}")
  # drop '#pragma once' in .c file to avoid warning
  string(REPLACE "#pragma once" "" LEAN_H "${LEAN_H}")
  file(WRITE "${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c" "${LEAN_H}")
  message("Generating LLVM bitcode file for Lean runtime at '${CMAKE_LIBRARY_OUTPUT_DIRECTORY}/lean.h.bc'")
  add_custom_command(
    OUTPUT ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc
    DEPENDS ${RUNTIME_OBJS} ${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c
    COMMAND
      bash -ec
      "${CMAKE_BINARY_DIR}/leanc.sh ${LEANC_OPTS} -I$<JOIN:$<TARGET_PROPERTY:leanrt_initial-exec,INCLUDE_DIRECTORIES>, -I> -c ${CMAKE_CURRENT_BINARY_DIR}/lean_inlines.c -emit-llvm -o ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc"
    VERBATIM
  )
  add_custom_target(runtime_bc DEPENDS ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/lean.h.bc)
endif()
