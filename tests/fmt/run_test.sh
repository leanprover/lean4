# `lean` does not link Lake, so Lake's builtin formatters only register when Lake is loaded as a
# plugin.
if [[ "$OSTYPE" == "cygwin" || "$OSTYPE" == "msys" ]]; then
  LAKE_PLUGIN="$BUILD_DIR/bin/libLake_shared.dll"
elif [[ "$OSTYPE" == darwin* ]]; then
  LAKE_PLUGIN="$BUILD_DIR/lib/lean/libLake_shared.dylib"
else
  LAKE_PLUGIN="$BUILD_DIR/lib/lean/libLake_shared.so"
fi

capture_only "$1" \
  lean -Dlinter.all=false --plugin="$LAKE_PLUGIN" --run run_test.lean "$1"
check_out_file
check_exit_is_success
