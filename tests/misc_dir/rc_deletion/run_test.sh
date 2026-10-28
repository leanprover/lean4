# Everything this test builds goes to $TMP_DIR, which util.sh removes afterwards.
lib="$TMP_DIR/lib"
mkdir -p "$lib"
build() { run env LEAN_PATH="$lib" lean -o "$lib/$1.olean" "$1.lean"; }

run lean --root=../../elab -Dlinter.all=false -o "$lib/rc_model.olean" ../../elab/rc_model.lean
for m in Counts Graph Schedule Heap Refinement; do build $m; done
run env LEAN_PATH="$lib" lean Examples.lean

# heaps.c releases the roots of random heaps through the runtime; Replay.lean requires `drain` to
# reclaim the same objects and leave the same counts.
run leanc ${LEANC_OPTS-} -o "$TMP_DIR/heaps" heaps.c
run "$TMP_DIR/heaps" > "$TMP_DIR/corpus"
run env LEAN_PATH="$lib" lean --run Replay.lean "$TMP_DIR/corpus"
