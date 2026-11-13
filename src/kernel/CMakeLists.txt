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
  init_module.cpp
  trace.cpp
)

# Counts and indices in the kernel are `size_t`: a lossy implicit conversion can alias distinct values.
# Clang only, as GCC's `-Wconversion` also reports safe arithmetic.
if(CMAKE_CXX_COMPILER_ID MATCHES "Clang")
  target_compile_options(kernel PRIVATE -Werror=conversion)
endif()
