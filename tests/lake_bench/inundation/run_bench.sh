PREFIX="lake/inundation"
rm -f measurements.jsonl

echo "Running $PREFIX"
rm -rf .lake lake-manifest.json test
lake -R run mkBuild

echo "Running $PREFIX/build/no-op"
lake -R clean
lake build
"$TEST_DIR/measure.py" -t "$PREFIX/build/no-op" -d -a -- \
  lake build

echo "Running $PREFIX/build/clean"
lake -R clean
"$TEST_DIR/measure.py" -t "$PREFIX/build/clean" -d -a -- \
  lake build

echo "Running $PREFIX/build/precompile/no-op"
lake -R -K precompile=true clean
lake build
"$TEST_DIR/measure.py" -t "$PREFIX/build/precompile/no-op" -d -a -- \
  lake build

echo "Running $PREFIX/build/precompile/clean"
lake -R -K precompile=true clean
"$TEST_DIR/measure.py" -t "$PREFIX/build/precompile/clean" -d -a -- \
  lake build

echo "Running $PREFIX/config/elab"
lake -R run nop
"$TEST_DIR/measure.py" -t "$PREFIX/config/elab" -d -a -- \
  lake -R run nop

echo "Running $PREFIX/config/import"
lake -R run nop
"$TEST_DIR/measure.py" -t "$PREFIX/config/import" -d -a -- \
  lake run nop

echo "Running $PREFIX/config/tree"
lake -R run mkTree
lake -d test/tree update
"$TEST_DIR/measure.py" -t "$PREFIX/config/tree" -d -a -- \
  lake -d test/tree run nop

echo "Running $PREFIX/env"
lake -R env true
"$TEST_DIR/measure.py" -t "$PREFIX/env" -d -a -- \
  lake env true

echo "Running $PREFIX/startup"
"$TEST_DIR/measure.py" -t "$PREFIX/startup" -d -a -- \
  lake self-check
