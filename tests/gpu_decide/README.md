# GPU Decide Tests

This directory contains tests and benchmarks for the GPU-accelerated `decide` tactic.

## Files

- `GpuDecideTest.lean` — Basic functionality tests
- `Benchmark.lean` — Performance benchmarks

## Running Tests

```bash
# Run all tests
lean --make tests/gpu_decide/*.lean

# Run benchmarks
lean --run tests/gpu_decide/Benchmark.lean
```

## Expected Results

All tests should pass with `decide` routing through the GPU handler
when a CUDA-capable GPU is available.
