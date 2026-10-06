# Collector regression

Run `tests/with_stage1_test_env.sh tests/misc_dir/rc_graph/run_test.sh` from the
repository root.

See the [runtime README](../../../src/runtime/lean/README.md) for generation, bootstrap,
proofs, validation gates, and benchmarks, and [CONTRACTS.md](../../../src/runtime/lean/CONTRACTS.md) for native assumptions.

Scratch files stay under this test's `_tmp/`. `candidate.c` exercises ignored null
physical slots before migration; `native_contracts.c` checks the incumbent runtime.
