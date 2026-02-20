cd ../../src

exec_capture "$FILE" \
  "$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" -- \
  lean --run "$SCRIPT_DIR/benchReelabWatchdogRss.lean" lean Init/Data/List/Sublist.lean 10 -j4

extract_measurements "$FILE" "$TOPIC"
