PREFIX="lake/inundation"
rm -f measurements.jsonl

echo "Running $PREFIX"
rm -rf .lake lake-manifest.json test
lake -R run mkBuild

bench_build() {
  local name=$1; shift
  echo "Running $PREFIX/$name/no-op"
  lake -R "$@" clean
  lake build
  "$TEST_DIR/measure.py" -t "$PREFIX/$name/no-op" -d -a -- \
    lake build

  echo "Running $PREFIX/$name/clean"
  lake -R "$@" clean
  "$TEST_DIR/measure.py" -t "$PREFIX/$name/clean" -d -a -- \
    lake build
}

bench_build build
bench_build precompileModules -K precompileModules=true
bench_build precompileLibrary -K precompileLibrary=true

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
