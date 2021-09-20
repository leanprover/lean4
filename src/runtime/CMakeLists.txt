set(RUNTIME_OBJS debug.cpp thread.cpp mpz.cpp mpq.cpp utf8.cpp
object.cpp apply.cpp exception.cpp interrupt.cpp memory.cpp
stackinfo.cpp compact.cpp init_module.cpp io.cpp hash.cpp
platform.cpp alloc.cpp allocprof.cpp sharecommon.cpp stack_overflow.cpp
process.cpp object_ref.cpp)
add_library(leanrt_initial-exec STATIC ${RUNTIME_OBJS})
set_target_properties(leanrt_initial-exec PROPERTIES
  ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_CURRENT_BINARY_DIR})

# The above library, like all other C++ code, is built using `-ftls-model=initial-exec`, which is necessary for linking it into `leanshared`,
# but introduces a measurable overhead while accessing the thread-local variable `g_heap` when allocating and deallocating. Therefore we compile
# the runtime again with the more restrictive `local-exec` and use it when linking Lean code statically, i.e. not against `leanshared`.
string(REPLACE ";" " " RUNTIME_OBJS_STR "${RUNTIME_OBJS}")
string(TOUPPER "${CMAKE_BUILD_TYPE}" uppercase_CMAKE_BUILD_TYPE)
add_custom_command(
  OUTPUT ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/libleanrt.a
  DEPENDS ${RUNTIME_OBJS}
  # compile each runtime file with the original compile flags plus `-ftls-model=local-exec`
  COMMAND bash -ec "rm -rf runtmp2 || true; mkdir runtmp2; for f in ${RUNTIME_OBJS_STR}; do ${CMAKE_CXX_COMPILER_LAUNCHER} ${CMAKE_CXX_COMPILER} ${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}} ${CMAKE_CXX_FLAGS} ${CMAKE_CXX_SYSROOT_FLAG}${CMAKE_OSX_SYSROOT} ${CMAKE_CXX_OSX_DEPLOYMENT_TARGET_FLAG}${CMAKE_OSX_DEPLOYMENT_TARGET} -ftls-model=local-exec -I$<JOIN:$<TARGET_PROPERTY:leanrt_initial-exec,INCLUDE_DIRECTORIES>, -I> \"${CMAKE_CURRENT_SOURCE_DIR}/$f\" -c -o runtmp2/$f.o; done; ar rcs ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/libleanrt.a runtmp2/*.o"
  VERBATIM)
add_custom_target(leanrt ALL DEPENDS ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}/libleanrt.a)

if(LLVM)
  add_custom_command(
    OUTPUT libleanrt.bc
    DEPENDS ${RUNTIME_OBJS} lean_inlines.c
    # compile each runtime file with the original compile flags plus `-emit-llvm`, then `llvm-link` them together
    COMMAND bash -ec "rm -rf runtmp || true; mkdir runtmp; for f in ${RUNTIME_OBJS_STR} lean_inlines.c; do ${CMAKE_CXX_COMPILER_LAUNCHER} ${CMAKE_CXX_COMPILER} ${CMAKE_CXX_FLAGS} ${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}} -I$<JOIN:$<TARGET_PROPERTY:leanrt_initial-exec,INCLUDE_DIRECTORIES>, -I> $([[ $f = \*.cpp ]] || echo \"-x c\") \"${CMAKE_CURRENT_SOURCE_DIR}/$f\" -S -emit-llvm -o runtmp/$f.ll; done; llvm-link runtmp/*.ll -o libleanrt.bc"
    VERBATIM)
  add_custom_target(runtime_bc DEPENDS libleanrt.bc)
endif()
