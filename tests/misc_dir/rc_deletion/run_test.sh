# Everything this test builds goes to $TMP_DIR, which util.sh removes afterwards.
lib="$TMP_DIR/lib"
mkdir -p "$lib"
build() { run env LEAN_PATH="$lib" lean -o "$lib/$1.olean" "$1.lean"; }

run lean --root=../../elab -Dlinter.all=false -o "$lib/rc_model.olean" ../../elab/rc_model.lean
for m in Counts Graph Schedule; do build $m; done
run env LEAN_PATH="$lib" lean Examples.lean
