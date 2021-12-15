set(RUNTIME_OBJS debug.cpp thread.cpp mpz.cpp utf8.cpp
object.cpp apply.cpp exception.cpp interrupt.cpp memory.cpp
stackinfo.cpp compact.cpp init_module.cpp load_dynlib.cpp io.cpp hash.cpp
platform.cpp alloc.cpp allocprof.cpp sharecommon.cpp stack_overflow.cpp
process.cpp object_ref.cpp mpn.cpp)
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

if(LLVM)
  add_custom_command(
    OUTPUT libleanrt.bc
    DEPENDS ${RUNTIME_OBJS} lean_inlines.c
    # compile each runtime file with the original compile flags plus `-emit-llvm`, then `llvm-link` them together
    COMMAND bash -ec "rm -rf runtmp || true; mkdir runtmp; for f in ${RUNTIME_OBJS_STR} lean_inlines.c; do ${CMAKE_CXX_COMPILER_LAUNCHER} ${CMAKE_CXX_COMPILER} ${CMAKE_CXX_FLAGS} ${LEANC_OPTS} -I$<JOIN:$<TARGET_PROPERTY:leanrt_initial-exec,INCLUDE_DIRECTORIES>, -I> $([[ $f = \*.cpp ]] || echo \"-x c\") \"${CMAKE_CURRENT_SOURCE_DIR}/$f\" -S -emit-llvm -o runtmp/$f.ll; done; llvm-link runtmp/*.ll -o libleanrt.bc"
    VERBATIM)
  add_custom_target(runtime_bc DEPENDS libleanrt.bc)
endif()
