STAGE_THIS="stage$STAGE"
STAGE_NEXT="stage$((STAGE + 1))"

BUILD_ROOT="$(realpath "$BUILD_DIR/..")"
BUILD_THIS="$(realpath "$BUILD_ROOT/$STAGE_THIS")"
BUILD_NEXT="$(realpath "$BUILD_ROOT/$STAGE_NEXT")"

OUT="$(realpath measurements.jsonl)"



echo
echo ">"
echo "> Configuring $STAGE_NEXT..."
echo ">"

make -C "$BUILD_ROOT" -j"$(nproc)" "$STAGE_NEXT-configure"



echo
echo ">"
echo "> Building $STAGE_NEXT..."
echo ">"

make -C "$BUILD_NEXT" clean-stdlib

LAKE_OVERRIDE_LEAN=true LEAN="$(realpath fake_root/bin/lean)" \
WRAPPER_PREFIX="$(realpath fake_root)" WRAPPER_OUT="$OUT" \
  lakeprof record -- \
  "$TEST_DIR/measure.py" -t build -d -a -- \
  make -C "$BUILD_NEXT" -j"$(nproc)" make_stdlib LAKE_EXTRA_ARGS="+Init:olean +Std:olean +Lean:olean +Lake:olean +LakeMain:olean +LeanIR:olean +Leanc:olean +LeanChecker:olean"



echo
echo ">"
echo "> Analyzing lakeprof data..."
echo ">"

# Lakeprof must be executed in the src dir because it obtains some metadata by
# calling lake in its current working directory.
mv lakeprof.log "$SRC_DIR"
pushd "$SRC_DIR"
lakeprof report -prc > lakeprof_report.txt
lakeprof report -pj | jq '{metric: "build/lakeprof/longest build path//wall-clock", value: .[-1][2], unit: "s"}' -c >> "$OUT"
lakeprof report -rj | jq '{metric: "build/lakeprof/longest rebuild path//wall-clock", value: .[-1][2], unit: "s"}' -c >> "$OUT"
popd
