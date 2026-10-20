mkdir -p _tmp
run lean --root=../../elab -o _tmp/rc_model.olean ../../elab/rc_model.lean
run env LEAN_PATH=_tmp lean -o _tmp/Concurrent.olean Concurrent.lean
run lean --root="$SRC_DIR/runtime/lean" -o _tmp/Collector.olean \
    "$SRC_DIR/runtime/lean/Collector.lean"
run lean NativeContracts.lean
run env LEAN_PATH=_tmp lean Dispatch.lean
run env LEAN_PATH=_tmp lean -o _tmp/Graph.olean Graph.lean
run env LEAN_PATH=_tmp lean -o _tmp/Schedule.olean Schedule.lean
run env LEAN_PATH=_tmp lean -o _tmp/Refinement.olean Refinement.lean
run env LEAN_PATH=_tmp lean ConcurrentRefinement.lean
run env LEAN_PATH=_tmp lean Examples.lean

run lean --run "$SCRIPT_DIR/gen_gc.lean" "$SRC_DIR/runtime/lean/Collector.lean" \
    _tmp/object_gc.inc
run diff -u "$SRC_DIR/runtime/object_gc.inc" _tmp/object_gc.inc
run python3 audit.py "$SCRIPT_DIR/gen_gc.lean" "$SRC_DIR/runtime/lean/Collector.lean"

run leanc ${LEANC_OPTS-} -I_tmp -o _tmp/candidate candidate.c
run ./_tmp/candidate
run python3 refinement_audit.py "$SCRIPT_DIR/gen_gc.lean" "$SRC_DIR/runtime/lean/Collector.lean"

run leanc ${LEANC_OPTS-} -o _tmp/native native.c
run ./_tmp/native
run leanc ${LEANC_OPTS-} -o _tmp/native_contracts native_contracts.c
run ./_tmp/native_contracts
run leanc ${LEANC_OPTS-} -o _tmp/concurrent concurrent.c
run ./_tmp/concurrent
