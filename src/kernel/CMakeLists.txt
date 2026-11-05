add_library(
  kernel
  OBJECT
  level.cpp
  expr.cpp
  expr_eq_fn.cpp
  for_each_fn.cpp
  replace_fn.cpp
  abstract.cpp
  instantiate.cpp
  local_ctx.cpp
  declaration.cpp
  environment.cpp
  type_checker.cpp
  init_module.cpp
  quot.cpp
  inductive.cpp
  trace.cpp
)

# Counts and indices in the kernel are `size_t`: truncating them to 32 bits can alias distinct values.
# `lean.h` is exempt as it is not kernel code; GCC and MSVC have no equivalent of this warning.
if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  target_compile_options(kernel PRIVATE -Werror=shorten-64-to-32 --system-header-prefix=lean/)
endif()
