mkdir -p _tmp
run lean --root=../../elab -o _tmp/rc_model.olean ../../elab/rc_model.lean
run env LEAN_PATH=_tmp lean -o _tmp/Concurrent.olean Concurrent.lean
run lean --root="$SRC_DIR/runtime/lean" -o _tmp/Collector.olean "$SRC_DIR/runtime/lean/Collector.lean"
run lean NativeContracts.lean
run env LEAN_PATH=_tmp lean Dispatch.lean
run env LEAN_PATH=_tmp lean -o _tmp/Graph.olean Graph.lean
run env LEAN_PATH=_tmp lean -o _tmp/Schedule.olean Schedule.lean
run env LEAN_PATH=_tmp lean -o _tmp/Refinement.olean Refinement.lean
run env LEAN_PATH=_tmp lean ConcurrentRefinement.lean
run env LEAN_PATH=_tmp lean Examples.lean

run leanc ${LEANC_OPTS-} -o _tmp/native native.c
run ./_tmp/native
run leanc ${LEANC_OPTS-} -o _tmp/native_contracts native_contracts.c
run ./_tmp/native_contracts
run leanc ${LEANC_OPTS-} -o _tmp/concurrent concurrent.c
run ./_tmp/concurrent
