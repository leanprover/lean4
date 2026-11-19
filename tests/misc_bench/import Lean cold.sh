cd ../../src
# Like `import Lean`, but drop the built library files from the page cache first for a cold-cache run.
"$TEST_DIR/evict.py" "$BUILD_DIR/lib/lean/**/*"
"$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" -- \
  lean --setup="$BUILD_DIR/lib/temp/Lean.setup.json" Lean.lean
