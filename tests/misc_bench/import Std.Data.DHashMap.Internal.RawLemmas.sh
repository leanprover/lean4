cd ../../src
"$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" -- \
  lean Std/Data/DHashMap/Internal/RawLemmas.lean
