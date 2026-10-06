# Reference-counting regression

Run `tests/with_stage1_test_env.sh tests/misc_dir/rc_graph/run_test.sh` from the
repository root.

The native graph tests check the existing runtime against a counted-edge oracle.
`concurrent.c` checks retained payloads and exactly-once finalization with eight workers.
`Graph.lean` models serial deletion; `Schedule.lean` proves that every deletion
schedule reaches the same state and states what a release does.
The native memory regressions and `NativeContracts.lean` check representation
and effect contracts; see [CONTRACTS.md](../../../src/runtime/lean/CONTRACTS.md)
for assumptions and limits.
`Refinement.lean`, `Dispatch.lean` and `Examples.lean` certify the shared Lean
candidate while the runtime continues to use the existing collector.

Scratch files stay under this test's `_tmp/`.
`Concurrent.lean` proves the shared-counter ownership invariant across guard/update histories.
`ConcurrentRefinement.lean` binds the production release decision to that invariant.
