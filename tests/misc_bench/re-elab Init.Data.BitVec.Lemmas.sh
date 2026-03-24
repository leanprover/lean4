cd ../../src

capture_only "$FILE" \
  "$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" -- \
  lean --run "$SCRIPT_DIR/benchReelabRss.lean" lean Init/Data/BitVec/Lemmas.lean 3 -j4
check_exit_is_success
extract_measurements "$TOPIC"
