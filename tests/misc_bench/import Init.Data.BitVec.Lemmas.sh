cd ../../src
"$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" -- \
  lean Init/Data/BitVec/Lemmas.lean
