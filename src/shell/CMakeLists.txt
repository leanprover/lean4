add_library(leanmain STATIC lean.cpp)
set_target_properties(leanmain PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib/temp OUTPUT_NAME leanmain)

# library must contain at least one non-manifest file
# We use `CONFIGURE` instead of `WRITE` so as to avoid touching the file on each run
file(CONFIGURE OUTPUT ${CMAKE_BINARY_DIR}/temp/empty.c CONTENT "")
add_library(leanmanifest STATIC ${CMAKE_BINARY_DIR}/temp/empty.c manifest.rc)
set_target_properties(
  leanmanifest
  PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_BINARY_DIR}/lib/lean OUTPUT_NAME leanmanifest
)

if(LLVM)
  if(CMAKE_SYSTEM_NAME MATCHES "Linux")
    set(LLVM_SYSTEM_LIBS "-lz -ltinfo")
  elseif(CMAKE_SYSTEM_NAME MATCHES "Darwin")
    # macOS doesn't have -Bstatic, so let cmake search for the libraries
    find_library(LIBZ NAMES z REQUIRED)
    find_library(NCURSES NAMES ncurses REQUIRED)
    set(LLVM_SYSTEM_LIBS "${LIBZ} ${NCURSES}")
  else()
    set(LLVM_SYSTEM_LIBS "-lz")
  endif()
  if(NOT CMAKE_SYSTEM_NAME MATCHES "Darwin")
    string(
      APPEND LEAN_EXE_LINKER_FLAGS
      " `llvm-config --link-static --ldflags --libs nativecodegen` -Wl,-Bstatic ${LLVM_SYSTEM_LIBS} -Wl,-Bdynamic"
    )
  else()
    string(APPEND LEAN_EXE_LINKER_FLAGS " `llvm-config --ldflags --libs nativecodegen` ${LLVM_SYSTEM_LIBS}")
  endif()
  if(CMAKE_SYSTEM_NAME MATCHES "Windows")
    string(APPEND LEAN_EXE_LINKER_FLAGS " -lole32 -luuid")
  endif()
endif()

add_custom_target(
  lean
  ALL
  WORKING_DIRECTORY ${LEAN_SOURCE_DIR}
  DEPENDS leanshared leanmain
  COMMAND $(MAKE) -f ${CMAKE_BINARY_DIR}/stdlib.make lean
  COMMAND_EXPAND_LISTS
)
