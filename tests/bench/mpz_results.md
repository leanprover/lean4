# Bignum allocation benchmark

EPYC 9455, GMP 6.3.0, Clang 22, release/mimalloc; medians of nine paired runs on CPU 5 against `dc34e5f5cf9c42dd783471b525abbe66c0194270`.

| Operation | Bits | Copying ns/op | Moving ns/op | GMP allocations, before → after |
| --- | ---: | ---: | ---: | ---: |
| GMP-to-Lean bridge | 4096 | 42.3 | 32.1 | 2 → 1 |
| Int negation | 4096 | 45.6 | 36.2 | 2 → 1 |
| Int multiplication | 4096 | 1428.1 | 1561.7 | 4 → 3 |
| Nat addition (unchanged control) | 256 | 46.7 | 45.0 | 3 → 3 |

Moving saves one limb allocation and copy. Conversion gains reproduced on a second core; arithmetic timings were noisy on this shared machine. Copying results with capacity above twice the used limb count bounds retained spare storage.

Build matching base and optimized release worktrees. Set `GMP_INCLUDE` and `GMP_LIBRARY` from the CMake cache, then compile this harness once and run it against each runtime:

```sh
c++ -O3 -DNDEBUG -std=c++17 -I"$BASE_WORKTREE/build/release/stage1/include" -I"$GMP_INCLUDE" tests/bench/mpz_results.cpp -L"$BASE_WORKTREE/build/release/stage1/lib/lean" -lleanshared "$GMP_LIBRARY" -o /tmp/mpz-results-bench
LD_LIBRARY_PATH="$BASE_WORKTREE/build/release/stage1/lib/lean" taskset -c 5 /tmp/mpz-results-bench
LD_LIBRARY_PATH="$MOVE_WORKTREE/build/release/stage1/lib/lean" taskset -c 5 /tmp/mpz-results-bench
```

Alternate run order across nine pairs. Use `--allocations` for allocation/retention counts and `--capacity` for small-result/large-operand cases.
