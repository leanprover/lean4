cd ../../src

exec_capture "$FILE" \
  "$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" -- \
  lean --run "$SCRIPT_DIR/benchReelabRss.lean" lean Init/Data/BitVec/Lemmas.lean 3 -j4

extract_measurements "$FILE" "$TOPIC"
