configure_file (
  "${LEAN_SOURCE_DIR}/shell/version.h.in"
  "${LEAN_BINARY_DIR}/version.h"
   )

include_directories("${LEAN_BINARY_DIR}")

include_directories (${LEAN_SOURCE_DIR}/util) 
include_directories (${LEAN_SOURCE_DIR}/numerics) 
set (EXTRA_LIBS ${EXTRA_LIBS} util numerics ${GMP_LIBRARIES})

set (CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} -pthread")

add_executable(lean lean.cpp)
target_link_libraries (lean ${EXTRA_LIBS})
