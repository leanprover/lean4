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
  expr_cache.cpp
  equiv_manager.cpp
  quot.cpp
  inductive.cpp
  trace.cpp
  instantiate_mvars.cpp
)

# GPU Type Checker (optional, requires CUDA)
option(LEAN_GPU "Enable GPU-accelerated type checking" ON)
if(LEAN_GPU)
    find_package(CUDAToolkit QUIET)
    if(CUDAToolkit_FOUND)
        enable_language(CUDA)
        set_source_files_properties(gpu_type_checker.cu PROPERTIES LANGUAGE CUDA)
        add_library(gpu_type_checker STATIC gpu_type_checker.cu)
        target_link_libraries(gpu_type_checker CUDA::cudart)
        target_include_directories(gpu_type_checker PUBLIC ${CMAKE_CURRENT_SOURCE_DIR})
        message(STATUS "GPU type checking enabled (CUDA ${CUDAToolkit_VERSION})")
    else()
        message(STATUS "GPU type checking disabled (CUDA not found)")
    endif()
endif()

