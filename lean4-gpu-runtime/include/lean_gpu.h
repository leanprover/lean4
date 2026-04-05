/*
 * Lean4 GPU Runtime Interface
 * 
 * This header defines the C-compatible interface for the GPU runtime.
 * It is implemented in gpu_runtime.cpp and linked into the Lean binary.
 */

#ifndef LEAN_GPU_H
#define LEAN_GPU_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// Opaque types for Lean runtime
typedef struct lean_obj lean_obj;
typedef lean_obj* lean_obj_arg;
typedef lean_obj* lean_obj_res;
typedef uint8_t b_obj_arg; // boxed object argument

/**
 * Get GPU device information.
 * Returns an Option GpuDeviceInfo.
 */
lean_obj_res lean_gpu_get_device_info(lean_obj_arg w);

/**
 * Get number of available CUDA devices.
 */
lean_obj_res lean_gpu_get_device_count(lean_obj_arg w);

/**
 * Batch evaluate Bool expressions on GPU.
 * 
 * @param exprs Array of serialized expressions (ByteArrays)
 * @param batchSize Maximum batch size
 * @param deviceId Target GPU device ID
 * @param w World token
 * @return Array Bool
 */
lean_obj_res lean_gpu_batch_eval_bool(lean_obj_arg exprs, b_obj_arg batchSize, b_obj_arg deviceId, lean_obj_arg w);

/**
 * Get GPU kernel execution time in milliseconds.
 */
lean_obj_res lean_gpu_get_timing_ms(lean_obj_arg w);

/**
 * Auto-tune batch size for the current GPU.
 */
lean_obj_res lean_gpu_autotune_batch(lean_obj_arg w);

#ifdef __cplusplus
}
#endif

#endif // LEAN_GPU_H
