# IO.Process.exit (used by the file worker) seems to be incompatible with LSAN
# TODO: investigate or work around
export ASAN_OPTIONS=detect_leaks=0

capture_only "$1" \
  lean -Dlinter.all=false --run run_test.lean "$1"
check_exit_is_success
check_out_file
