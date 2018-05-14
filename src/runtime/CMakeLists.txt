set(RUNTIME_OBJS debug.cpp thread.cpp mpz.cpp mpq.cpp
lean_obj.cpp apply.cpp exception.cpp interrupt.cpp memory.cpp
serializer.cpp stackinfo.cpp)
add_library(runtime OBJECT ${RUNTIME_OBJS})
add_library(leanruntime ${RUNTIME_OBJS})

ADD_CUSTOM_TARGET(bin_runtime ALL
  COMMAND "${CMAKE_COMMAND}" -E make_directory "${LEAN_SOURCE_DIR}/../bin"
  COMMAND "${CMAKE_COMMAND}" -E copy "${CMAKE_CURRENT_BINARY_DIR}/libleanruntime*" "${LEAN_SOURCE_DIR}/../bin"
  DEPENDS leanruntime
)
