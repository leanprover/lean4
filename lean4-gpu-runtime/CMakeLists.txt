# Lean4 GPU Runtime Package
# This package can be built separately or included via add_subdirectory.

cmake_minimum_required(VERSION 3.18)
project(Lean4GpuRuntime LANGUAGES CXX CUDA)

find_package(CUDAToolkit REQUIRED)

# Library target
add_library(lean_gpu_runtime STATIC
    src/gpu_runtime.cpp
    src/gpu_type_checker.cu
)

target_include_directories(lean_gpu_runtime PUBLIC
    ${CMAKE_CURRENT_SOURCE_DIR}/include
)

target_link_libraries(lean_gpu_runtime PUBLIC
    CUDA::cudart
)

# Compile definitions
target_compile_definitions(lean_gpu_runtime PRIVATE LEAN_CUDA)

# Install rules
install(TARGETS lean_gpu_runtime ARCHIVE DESTINATION lib)
install(DIRECTORY include/ DESTINATION include)
