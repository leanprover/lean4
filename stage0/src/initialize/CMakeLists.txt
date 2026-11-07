add_library(initialize OBJECT init.cpp)

# `leanchecker` only replays declarations through the kernel; it never elaborates Lean source, so it
# does not need `initialize_Lean` and the whole library it drags in. Only this file varies, so a
# second copy of it suffices, linked ahead of `libleancpp.a` so its `lean_initialize` wins.
add_library(initialize_minimal STATIC EXCLUDE_FROM_ALL init.cpp)
set_target_properties(
  initialize_minimal
  PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}
)
target_compile_definitions(initialize_minimal PRIVATE LEAN_MINIMAL_CORE_INIT)

# `leanir` never elaborates Lean source either but links against `libleanshared`, so it selects the
# minimal initialization at run time instead; see `init_minimal_shim.c`.
add_library(initialize_minimal_shim STATIC EXCLUDE_FROM_ALL init_minimal_shim.c)
set_target_properties(
  initialize_minimal_shim
  PROPERTIES ARCHIVE_OUTPUT_DIRECTORY ${CMAKE_ARCHIVE_OUTPUT_DIRECTORY}
)
