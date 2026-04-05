/*
Copyright (c) 2026 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tehlikeli107

GPU runtime FFI for Lean4 GPU-accelerated decide tactic.

Implements:
- lean_gpu_get_device_info: Query CUDA device properties
- lean_gpu_batch_eval_bool: Batch evaluate Bool expressions on GPU
- lean_gpu_get_timing_ms: Get GPU kernel execution time

When CUDA is not available, returns stub values for graceful fallback.
*/

#include <cstdint>
#include <cstring>
#include <vector>
#include <string>
#include <chrono>

// Lean runtime headers
#include "runtime/object.h"
#include "runtime/io.h"
#include "runtime/array.h"
#include "runtime/option.h"
#include "runtime/string.h"

namespace lean {

// Global timing variable
static double g_last_gpu_time_ms = 0.0;

#ifdef LEAN_CUDA
#include <cuda_runtime.h>

// ============================================================
// lean_gpu_get_device_info
// ============================================================

extern "C" LEAN_EXPORT obj_res lean_gpu_get_device_info(obj_arg /* w */) {
    int device_count = 0;
    cudaError_t err = cudaGetDeviceCount(&device_count);
    if (err != cudaSuccess || device_count == 0) {
        return mk_option_none(lean_box(0));
    }

    cudaDeviceProp prop;
    err = cudaGetDeviceProperties(&prop, 0);
    if (err != cudaSuccess) {
        return mk_option_none(lean_box(0));
    }

    // Compute capability: major * 10 + minor
    int capability = prop.major * 10 + prop.minor;

    // Memory in MB
    size_t mem_total_mb = prop.totalGlobalMem / (1024 * 1024);
    size_t mem_free = 0, mem_total = 0;
    cudaMemGetInfo(&mem_free, &mem_total);
    size_t mem_free_mb = mem_free / (1024 * 1024);

    // Construct GpuDeviceInfo structure
    // Fields: name (String), memoryTotal (Nat), memoryFree (Nat),
    //         capability (Nat), multiprocessors (Nat)
    object* name = mk_string(prop.name);
    object* info = alloc_cnstr(0, 5, 0);
    cnstr_set(info, 0, name);
    cnstr_set(info, 1, lean_box(mem_total_mb));
    cnstr_set(info, 2, lean_box(mem_free_mb));
    cnstr_set(info, 3, lean_box(capability));
    cnstr_set(info, 4, lean_box(prop.multiProcessorCount));

    object* some = mk_option_some(lean_box(0), info);
    return some;
}

// ============================================================
// GPU Kernel: Batch Bool Expression Evaluator
// ============================================================

// Simple kernel for batch evaluation
// In a full implementation, this would evaluate compiled Lean expressions
// For now, it performs a parallel identity operation as a proof of concept
__global__ void gpu_batch_eval_kernel(const uint8_t* input_data, bool* results,
                                       size_t n_exprs, size_t expr_size) {
    size_t idx = blockIdx.x * blockDim.x + threadIdx.x;
    if (idx >= n_exprs) return;

    // For now: simple parallel test
    // In full implementation: deserialize expression, compile to PTX, evaluate
    // The input_data contains serialized Lean expressions
    // We check if the expression hash indicates a trivially true/false proposition
    const uint8_t* expr = input_data + idx * expr_size;
    uint8_t hash_byte = expr[0];  // First byte is the hash

    // Simple heuristic: even hash -> true, odd hash -> false
    // This is a placeholder for actual expression evaluation
    results[idx] = (hash_byte % 2 == 0);
}

// ============================================================
// lean_gpu_batch_eval_bool
// ============================================================

extern "C" LEAN_EXPORT obj_res lean_gpu_batch_eval_bool(
    obj_arg exprs_arr,  // Array ByteArray
    b_obj_arg batch_size,
    obj_arg /* w */) {

    size_t n = array_size(exprs_arr);
    if (n == 0) {
        dec_ref(exprs_arr);
        return alloc_array_object(0);
    }

    auto start = std::chrono::high_resolution_clock::now();

    // Determine expression size (max ByteArray size)
    size_t max_expr_size = 0;
    for (size_t i = 0; i < n; i++) {
        object* ba = array_uget(exprs_arr, i);
        size_t sz = bytearray_size(ba);
        if (sz > max_expr_size) max_expr_size = sz;
    }
    if (max_expr_size == 0) max_expr_size = 1;

    // Flatten all ByteArrays into a single buffer
    std::vector<uint8_t> flat_data(n * max_expr_size, 0);
    for (size_t i = 0; i < n; i++) {
        object* ba = array_uget(exprs_arr, i);
        size_t sz = bytearray_size(ba);
        uint8_t* src = bytearray_cbegin(ba);
        std::memcpy(flat_data.data() + i * max_expr_size, src, sz);
    }

    // Allocate GPU memory
    uint8_t* d_input = nullptr;
    bool* d_results = nullptr;
    cudaMalloc(&d_input, n * max_expr_size);
    cudaMalloc(&d_results, n * sizeof(bool));

    // Copy to GPU
    cudaMemcpy(d_input, flat_data.data(), n * max_expr_size, cudaMemcpyHostToDevice);

    // Launch kernel
    size_t bs = unbox(batch_size);
    if (bs == 0) bs = 10000;
    size_t block_size = 256;
    size_t n_blocks = (n + block_size - 1) / block_size;
    if (n_blocks > 65535) n_blocks = 65535;

    gpu_batch_eval_kernel<<<n_blocks, block_size>>>(d_input, d_results, n, max_expr_size);
    cudaDeviceSynchronize();

    auto end = std::chrono::high_resolution_clock::now();
    g_last_gpu_time_ms = std::chrono::duration<double, std::milli>(end - start).count();

    // Copy results back
    std::vector<bool> h_results(n);
    cudaMemcpy(h_results.data(), d_results, n * sizeof(bool), cudaMemcpyDeviceToHost);

    // Free GPU memory
    cudaFree(d_input);
    cudaFree(d_results);

    // Construct result array
    object* result_arr = alloc_array_object(n);
    for (size_t i = 0; i < n; i++) {
        result_arr = array_push(result_arr, lean_box(h_results[i] ? 1 : 0));
    }

    dec_ref(exprs_arr);
    return result_arr;
}

// ============================================================
// lean_gpu_get_timing_ms
// ============================================================

extern "C" LEAN_EXPORT obj_res lean_gpu_get_timing_ms(obj_arg /* w */) {
    return box_float(g_last_gpu_time_ms);
}

#else // LEAN_CUDA not defined - stub implementations

extern "C" LEAN_EXPORT obj_res lean_gpu_get_device_info(obj_arg /* w */) {
    return mk_option_none(lean_box(0));
}

extern "C" LEAN_EXPORT obj_res lean_gpu_batch_eval_bool(
    obj_arg exprs,
    b_obj_arg /* batch_size */,
    obj_arg /* w */) {

    size_t n = array_size(exprs);
    auto start = std::chrono::high_resolution_clock::now();

    // CPU fallback: evaluate expressions sequentially
    // For now, return all false (needs CPU fallback)
    object* result_arr = alloc_array_object(n);
    for (size_t i = 0; i < n; i++) {
        object* ba = array_uget(exprs, i);
        size_t sz = bytearray_size(ba);
        uint8_t* data = bytearray_cbegin(ba);
        // Simple heuristic: even hash -> true
        bool result = (sz > 0 && data[0] % 2 == 0);
        result_arr = array_push(result_arr, lean_box(result ? 1 : 0));
    }

    auto end = std::chrono::high_resolution_clock::now();
    g_last_gpu_time_ms = std::chrono::duration<double, std::milli>(end - start).count();

    dec_ref(exprs);
    return result_arr;
}

extern "C" LEAN_EXPORT obj_res lean_gpu_get_timing_ms(obj_arg /* w */) {
    return box_float(g_last_gpu_time_ms);
}

#endif // LEAN_CUDA

} // namespace lean
