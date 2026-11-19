cd ../../src
"$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" -- \
  lean --setup="$BUILD_DIR/lib/temp/Lean.setup.json" Lean.lean
