cd ../../src
# Like `import Lean`, but with `--evict`
"$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" --evict "$BUILD_DIR/lib/lean/**/*" -- \
  lean --setup="$BUILD_DIR/lib/temp/Lean.setup.json" Lean.lean
