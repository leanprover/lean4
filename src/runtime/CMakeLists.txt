set(RUNTIME_OBJS debug.cpp thread.cpp mpz.cpp mpq.cpp utf8.cpp
object.cpp apply.cpp exception.cpp interrupt.cpp memory.cpp
serializer.cpp stackinfo.cpp compact.cpp init_module.cpp io.cpp hash.cpp
platform.cpp alloc.cpp allocprof.cpp sharecommon.cpp stack_overflow.cpp
process.cpp)
add_library(runtime OBJECT ${RUNTIME_OBJS})
add_library(leanruntime ${RUNTIME_OBJS})
if(LLVM)
  string(REPLACE ";" " " RUNTIME_OBJS_STR "${RUNTIME_OBJS}")
  add_custom_command(
    OUTPUT libleanruntime.bc
    DEPENDS ${RUNTIME_OBJS}
    COMMAND sh -ec "rm -rf runtmp || true; mkdir runtmp; for f in ${RUNTIME_OBJS_STR}; do ${CMAKE_CXX_COMPILER_LAUNCHER} ${CMAKE_CXX_COMPILER} ${CMAKE_CXX_FLAGS_${uppercase_CMAKE_BUILD_TYPE}} -I$<JOIN:$<TARGET_PROPERTY:leanruntime,INCLUDE_DIRECTORIES>, -I> \"${CMAKE_CURRENT_SOURCE_DIR}/$f\" -S -emit-llvm -o runtmp/$f.bc; done; llvm-link runtmp/*.bc -o libleanruntime.bc"
    VERBATIM)
  add_custom_target(runtime_bc DEPENDS libleanruntime.bc)
endif()
