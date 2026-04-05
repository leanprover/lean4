# Lean4 Runtime CMakeLists.txt
# GPU desteği artık harici paket üzerinden (lean4-gpu-runtime)

# Standart runtime kaynakları
target_sources(stage0 PRIVATE
    alloc.cpp
    apply.cpp
    array.cpp
    bigint.cpp
    buffer.cpp
    checksum.cpp
    compact.cpp
    debug.cpp
    exception.cpp
    finalize.cpp
    flet.cpp
    format.cpp
    hash.cpp
    init.cpp
    io.cpp
    io_win.cpp
    kernel.cpp
    list_fn.cpp
    memory.cpp
    mpn.cpp
    name.cpp
    name_generator.cpp
    object.cpp
    option.cpp
    optional.cpp
    pair_ref.cpp
    platform.cpp
    process.cpp
    random.cpp
    rc.cpp
    ref.cpp
    sharecommon.cpp
    small_object_allocator.cpp
    stack_overflow.cpp
    string.cpp
    task.cpp
    thread.cpp
    timer.cpp
    utf8.cpp
)

# Windows specific
if(WIN32)
    target_sources(stage0 PRIVATE platform_win.cpp)
else()
    target_sources(stage0 PRIVATE platform_unix.cpp)
endif()

# GPU Runtime Integration (Optional)
# Bu, harici lean4-gpu-runtime paketini linkler.
option(LEAN_USE_GPU_RUNTIME "Link against external lean4-gpu-runtime" OFF)

if(LEAN_USE_GPU_RUNTIME)
    if(NOT TARGET lean_gpu_runtime)
        # FetchContent veya find_package ile dış paketi bul
        # Basitlik için doğrudan alt dizinden ekliyoruz:
        if(EXISTS "${CMAKE_CURRENT_SOURCE_DIR}/../../lean4-gpu-runtime/CMakeLists.txt")
            add_subdirectory("${CMAKE_CURRENT_SOURCE_DIR}/../../lean4-gpu-runtime" ${CMAKE_BINARY_DIR}/gpu_runtime)
        else()
            message(FATAL_ERROR "LEAN_USE_GPU_RUNTIME is ON but lean4-gpu-runtime package not found.")
        endif()
    endif()
    
    target_link_libraries(stage0 PRIVATE lean_gpu_runtime)
    message(STATUS "GPU Runtime linked successfully.")
else()
    message(STATUS "GPU Runtime disabled (default). Use -DLEAN_USE_GPU_RUNTIME=ON to enable.")
endif()
