# Bignum result allocation microbenchmark

`mpz_results.cpp` measures existing runtime entry points with copying or move-aware result allocation. It does not change the arithmetic algorithms or benchmark the extended-GCD backend.

## Representative results

AMD EPYC 9455, Linux x86-64, GMP 6.3.0, Clang 22.1.8, release builds with mimalloc. Both runtime builds use base revision `dc34e5f5cf9c42dd783471b525abbe66c0194270`; only the allocation, conversion, and capacity-check changes in `object.cpp`, `object.h`, and `mpz.h` differ. The optimized allocator copies when GMP capacity exceeds twice the used limb count; otherwise it moves. Times below are medians of nine alternating paired process runs pinned to logical CPU 5.

| Operation | Operand bits | Copying ns/op | Moving ns/op | Speedup | GMP allocations/op, before → after |
| --- | ---: | ---: | ---: | ---: | ---: |
| GMP-to-Lean bridge | 64 | 32.9 | 26.5 | 1.24× | 2 → 1 |
| Int addition | 64 | 48.7 | 45.9 | 1.06× | 3 → 2 |
| Int negation | 256 | 36.6 | 30.4 | 1.20× | 2 → 1 |
| Nat subtraction | 64 | 67.9 | 45.1 | 1.50× | 3 → 2 |
| Int decimal parsing | 64 | 76.5 | 51.3 | 1.49× | 2 → 1.75 |
| GMP-to-Lean bridge | 4096 | 42.3 | 32.1 | 1.32× | 2 → 1 |
| Int negation | 4096 | 45.6 | 36.2 | 1.26× | 2 → 1 |
| Int multiplication | 4096 | 1428.1 | 1561.7 | 0.91× | 4 → 3 |
| Int Euclidean division | 4096 | 2467.4 | 2561.7 | 0.96× | 3 → 2 |
| Nat addition (unchanged control) | 256 | 46.7 | 45.0 | 1.04× | 3 → 3 |
| Int cancellation to zero (control) | 4096 | 57.7 | 54.5 | 1.06× | 2 → 2 |

The moved heap-result paths eliminate one GMP allocation, one GMP free, and a limb copy. The capacity fallback preserves copying costs for unusually overallocated results: 12 of the 16 parsing inputs at 64 bits take this fallback. The bridge still copies its GMP argument once: its input is preserved, not consumed. Small results and copying lvalue paths retain their existing behavior. GMP reallocations are unchanged. These counts cover GMP limb storage, not Lean object allocations, which remain necessary.

Moving preserves some spare GMP capacity, bounded to twice the used limb count for nonzero heap results. In this corpus, signed Euclidean division and remainder retain one extra 8-byte limb: 4096-bit results use 520 rather than 512 bytes. Parsed results average 10 rather than 8 bytes at 64 bits and 522 rather than 512 bytes at 4096 bits. The bridge and the other measured operations retain the same output storage. Peak temporary limb storage is lower or unchanged; for the 4096-bit bridge it drops from 1024 to 512 bytes. This is a bounded memory/performance tradeoff, not a promise that every moved result has identical capacity.

The machine is shared, not exclusively reserved: the 64-bit bridge spans 27.6–43.7 ns before and 23.8–29.1 ns after. A separate nine-pair run on logical CPU 24 gives 1.30× for the 4096-bit bridge and 1.32× for 4096-bit negation, corroborating the larger conversion gains. Other estimates are less stable: that run gives 1.16× for 64-bit subtraction, 1.06× for 64-bit parsing, and 0.94× for the 64-bit bridge. Large multiplication ranges from 0.91× to 1.16× across the two runs; the cancellation control ranges from 0.84× to 1.06× despite unchanged allocations. Allocation reductions are deterministic, but neither these arithmetic timings nor all small-operation speedups are established. Do not extrapolate these microbenchmarks to whole-application speedups.

## Method

Use 16 deterministic, cache-hot input pairs per width, generated with GMP's Mersenne Twister and seed 15160. Cover 16, 32, 64, 256, 1024, and 4096 bits. Keep operands alive across calls and include result destruction in the timed region. Check every operation against independent GMP arithmetic and recheck retained inputs outside timing. For division, use a dividend `a * b + b / 2`, giving heap-sized quotients and, where representable, heap-sized remainders. Divide its negation for signed Euclidean division. Nat subtraction uses `(a + b) - b`; mixed Nat multiplication uses `a * 3`.

Each profile calibrates for at least 3 ms and then measures approximately 25 ms. Run copying/moving in alternating order across nine pairs of fresh processes, using the same harness executable. Collect allocation counts in separate processes with `--allocations`: only those processes install GMP memory hooks, so counting does not affect the timing runs. Counts exclude fixture creation and oracle checks and average across the 16 inputs.

The separate `--capacity` mode checks small results from large operands. Use `huge = 2^4096 + 1`, `small = 2^64`, `near = huge + small`, and `dividend = huge^2 + small`. Test Int/Nat subtraction, Int Euclidean remainder, Nat remainder, and a Nat gcd with similarly scaled operands. Every result equals `small` and retains 16 bytes in both builds. In particular, the capacity fallback prevents a small Euclidean remainder from retaining the large divisor's limb allocation.

## Reproduce

Build the base and optimized revisions with `cmake --preset release` and `make -j$(nproc) -C build/release` in separate worktrees, with matching release/GMP/mimalloc configuration. Compile the harness once, using the base worktree's public headers and the same GMP installation as both runtimes. Set `GMP_INCLUDE` and `GMP_LIBRARY` to the paths recorded in `build/release/stage1/CMakeCache.txt`.

```sh
c++ -O3 -DNDEBUG -std=c++17 -I"$BASE_WORKTREE/build/release/stage1/include" -I"$GMP_INCLUDE" tests/bench/mpz_results.cpp -L"$BASE_WORKTREE/build/release/stage1/lib/lean" -lleanshared "$GMP_LIBRARY" -Wl,-rpath,"$BASE_WORKTREE/build/release/stage1/lib/lean" -o /tmp/mpz-results-bench
LD_LIBRARY_PATH="$BASE_WORKTREE/build/release/stage1/lib/lean" taskset -c 5 /tmp/mpz-results-bench
LD_LIBRARY_PATH="$MOVE_WORKTREE/build/release/stage1/lib/lean" taskset -c 5 /tmp/mpz-results-bench
LD_LIBRARY_PATH="$BASE_WORKTREE/build/release/stage1/lib/lean" /tmp/mpz-results-bench --allocations
LD_LIBRARY_PATH="$MOVE_WORKTREE/build/release/stage1/lib/lean" /tmp/mpz-results-bench --allocations
LD_LIBRARY_PATH="$BASE_WORKTREE/build/release/stage1/lib/lean" /tmp/mpz-results-bench --capacity
LD_LIBRARY_PATH="$MOVE_WORKTREE/build/release/stage1/lib/lean" /tmp/mpz-results-bench --capacity
```

Repeat the timing commands nine times, alternating their order. Select a CPU available on the machine. Timing output is `op,bits,ns`; allocation output is `op,bits,allocs,reallocs,frees,requested_bytes,retained_bytes,peak_bytes`. Requested bytes sum allocation/reallocation sizes; retained bytes average the output's limb storage after the runtime call returns; peak bytes report the largest simultaneous live limb storage across the 16 calls. Each counting profile also checks that no counted storage remains after result destruction.
