source_init "$1"
run_before "$1"

TOPIC="elab/$(basename "$1" .lean)"

# `--root` to infer same private names as in the server
# Elab.inServer to allow for arbitrary `#eval`
capture_only "$1" \
  "$TEST_DIR/measure.py" -t "$TOPIC" -o "$1.measurements.jsonl" -d -- \
  lean --root=.. -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true "${TEST_LEAN_ARGS[@]}" "$1"
normalize_mvar_suffixes
normalize_reference_urls
extract_measurements "$TOPIC"
check_out_file
check_exit_is_success

run_after "$1"
