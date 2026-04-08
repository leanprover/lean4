source_init "$1"
run_before "$1"

# `--root` to infer same private names as in the server
# Elab.inServer to allow for arbitrary `#eval`
# compiler.postponeCompile for immediate trace output
capture_only "$1" \
  lean --root=.. -DprintMessageEndPos=true -Dlinter.all=false -DElab.inServer=true -Dcompiler.postponeCompile=false "${TEST_LEAN_ARGS[@]}" "$1"
normalize_mvar_suffixes
normalize_reference_urls
normalize_measurements
check_out_file
check_exit_is_success

run_after "$1"
