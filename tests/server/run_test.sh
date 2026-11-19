run_before "$1"

capture_only "$1" \
  lean "${LEAN_LINTER_ARGS[@]}" --run "$1"
check_out_file
check_exit_is_success

run_after "$1"
