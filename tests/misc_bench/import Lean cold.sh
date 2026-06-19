cd ../../src
# Like `import Lean`, but drop the built library files from the page cache first for a cold-cache run.

# `dd ... iflag=nocache count=0` issues `posix_fadvise(POSIX_FADV_DONTNEED)` for the whole file.
shopt -s globstar nullglob
evicted=0
for f in "$BUILD_DIR"/lib/lean/**/*; do
  if [ -f "$f" ]; then
    dd if="$f" iflag=nocache count=0 status=none
    evicted=1
  fi
done
shopt -u globstar nullglob
if [ "$evicted" -eq 0 ]; then
  echo "warning: no files were evicted from $BUILD_DIR/lib/lean" >&2
fi

"$TEST_DIR/measure.py" -t "$TOPIC" -d -o "$OUT" -- \
  lean --setup="$BUILD_DIR/lib/temp/Lean.setup.json" Lean.lean
