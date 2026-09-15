# Bignum result allocation microbenchmark

`mpz_results.cpp` measures existing runtime entry points with copying or move-aware result allocation. It does not change the arithmetic algorithms or benchmark the extended-GCD backend.

## Representative results

AMD EPYC 9455, Linux x86-64, GMP 6.3.0, Clang 22.1.8, release builds with mimalloc. Both runtime builds use base revision `dc34e5f5cf9c42dd783471b525abbe66c0194270`; only the allocation and conversion changes in `object.cpp` and `object.h` differ. Times are medians of nine alternating paired process runs pinned to logical CPU 24.

| Operation | Operand bits | Copying ns/op | Moving ns/op | Speedup | GMP allocations/op, before → after |
| --- | ---: | ---: | ---: | ---: | ---: |
| GMP-to-Lean bridge | 64 | 27.2 | 24.2 | 1.12× | 2 → 1 |
| Int addition | 64 | 43.0 | 39.6 | 1.09× | 3 → 2 |
| Int negation | 256 | 30.6 | 27.8 | 1.10× | 2 → 1 |
| Nat subtraction | 64 | 54.0 | 41.9 | 1.29× | 3 → 2 |
| Int decimal parsing | 64 | 55.7 | 43.6 | 1.28× | 2 → 1 |
| GMP-to-Lean bridge | 4096 | 36.7 | 27.7 | 1.33× | 2 → 1 |
| Int multiplication | 4096 | 1268.3 | 1249.8 | 1.01× | 4 → 3 |
| Int Euclidean division | 4096 | 2257.8 | 2253.2 | 1.00× | 3 → 2 |
| Nat addition (unchanged control) | 256 | 41.2 | 41.5 | 0.99× | 3 → 3 |
| Int cancellation to zero (control) | 256 | 30.6 | 30.4 | 1.00× | 2 → 2 |
| Int cancellation to zero (control) | 4096 | 47.8 | 50.7 | 0.94× | 2 → 2 |

The moved heap-result paths eliminate one GMP allocation, one GMP free, and a limb copy. The bridge still copies its GMP argument once: its input is preserved, not consumed. Small results and copying lvalue paths retain their existing behavior. GMP reallocations are unchanged. These counts cover GMP limb storage, not Lean object allocations, which remain necessary.

Moving also preserves GMP's allocated capacity instead of trimming it through a copy. In this corpus, signed Euclidean division and remainder retain one extra 8-byte limb: 4096-bit results use 520 rather than 512 bytes. Parsing also retains spare capacity: 64-bit parsed results average 22 rather than 8 bytes of limb storage, and 4096-bit parsed results average 522 rather than 512 bytes. The bridge and the other measured operations retain the same output storage. Peak temporary limb storage is lower or unchanged; for the 4096-bit bridge it drops from 1024 to 512 bytes. This is a memory/performance tradeoff, not a promise that every moved result has identical capacity.

Several inexpensive bignum operations improve by roughly 5–15%; parsing and some conversion/subtraction cases improve more. Arithmetic dominates large multiplication and division, so their small differences are within the noise. The 4096-bit cancellation control is about 6% slower despite unchanged allocations; improvements are not universal. The machine is shared, not exclusively reserved: for example, the 64-bit bridge spans 25.8–43.7 ns before and 22.9–37.8 ns after, although moving is faster in all nine paired samples. Do not interpret differences near 1–3% as established gains, or extrapolate these microbenchmarks to whole-application speedups.

## Method

Use 16 deterministic, cache-hot input pairs per width, generated with GMP's Mersenne Twister and seed 15160. Cover 16, 32, 64, 256, 1024, and 4096 bits. Keep operands alive across calls and include result destruction in the timed region. Check every operation against independent GMP arithmetic and recheck retained inputs outside timing. For division, use a dividend `a * b + b / 2`, giving heap-sized quotients and, where representable, heap-sized remainders. Divide its negation for signed Euclidean division. Nat subtraction uses `(a + b) - b`; mixed Nat multiplication uses `a * 3`.

Each profile calibrates for at least 3 ms and then measures approximately 25 ms. Run copying/moving in alternating order across nine pairs of fresh processes, using the same harness executable. Collect allocation counts in separate processes with `--allocations`: only those processes install GMP memory hooks, so counting does not affect the timing runs. Counts exclude fixture creation and oracle checks and average across the 16 inputs.

## Reproduce

Build the base and optimized revisions with `cmake --preset release` and `make -j$(nproc) -C build/release` in separate worktrees, with matching release/GMP/mimalloc configuration. Compile the harness once, using the base worktree's public headers and the same GMP installation as both runtimes. Set `GMP_INCLUDE` and `GMP_LIBRARY` to the paths recorded in `build/release/stage1/CMakeCache.txt`.

```sh
c++ -O3 -DNDEBUG -std=c++17 -I"$BASE_WORKTREE/build/release/stage1/include" -I"$GMP_INCLUDE" tests/bench/mpz_results.cpp -L"$BASE_WORKTREE/build/release/stage1/lib/lean" -lleanshared "$GMP_LIBRARY" -Wl,-rpath,"$BASE_WORKTREE/build/release/stage1/lib/lean" -o /tmp/mpz-results-bench
LD_LIBRARY_PATH="$BASE_WORKTREE/build/release/stage1/lib/lean" taskset -c 24 /tmp/mpz-results-bench
LD_LIBRARY_PATH="$MOVE_WORKTREE/build/release/stage1/lib/lean" taskset -c 24 /tmp/mpz-results-bench
LD_LIBRARY_PATH="$BASE_WORKTREE/build/release/stage1/lib/lean" /tmp/mpz-results-bench --allocations
LD_LIBRARY_PATH="$MOVE_WORKTREE/build/release/stage1/lib/lean" /tmp/mpz-results-bench --allocations
```

Repeat the timing commands nine times, alternating their order. Select a CPU available on the machine. Timing output is `op,bits,ns`; allocation output is `op,bits,allocs,reallocs,frees,requested_bytes,retained_bytes,peak_bytes`. Requested bytes sum allocation/reallocation sizes; retained bytes average the output's limb storage after the runtime call returns; peak bytes report the largest simultaneous live limb storage across the 16 calls. Each counting profile also checks that no counted storage remains after result destruction.
