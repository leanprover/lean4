source_init "$1"
run_before "$1"

# `--root` to infer same private names as in the server
# Elab.inServer to allow for arbitrary `#eval`
capture_only "$1" \
  lean --root=.. -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true "${TEST_LEAN_ARGS[@]}" "$1"
check_exit_is_fail
normalize_mvar_suffixes
normalize_reference_urls
normalize_measurements
check_out_file

run_after "$1"
