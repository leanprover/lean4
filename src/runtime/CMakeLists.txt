set(RUNTIME_OBJS debug.cpp thread.cpp mpz.cpp mpq.cpp utf8.cpp
object.cpp apply.cpp exception.cpp interrupt.cpp memory.cpp
serializer.cpp stackinfo.cpp compact.cpp init_module.cpp io.cpp hash.cpp
platform.cpp alloc.cpp allocprof.cpp sharecommon.cpp stack_overflow.cpp
process.cpp)
add_library(runtime OBJECT ${RUNTIME_OBJS})
add_library(leanruntime ${RUNTIME_OBJS})
