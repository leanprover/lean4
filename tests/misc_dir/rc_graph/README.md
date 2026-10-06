# Collector regression

Run `tests/with_stage1_test_env.sh tests/misc_dir/rc_graph/run_test.sh` from the
repository root.

See the [runtime README](../../../src/runtime/lean/README.md) for generation, bootstrap,
proofs, validation gates, and benchmarks, and [CONTRACTS.md](../../../src/runtime/lean/CONTRACTS.md) for native assumptions.

Scratch files stay under this test's `_tmp/`. Null constructor, closure, and array
slot fixtures in `native_contracts.c` require the migrated runtime.
