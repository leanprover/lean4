# IO.Process.exit (used by the file worker) seems to be incompatible with LSAN
# TODO: investigate or work around
export ASAN_OPTIONS=detect_leaks=0

lake build

FILE=InverseModuleHierarchy/BasicTest.lean
capture_only "$FILE" \
  lean -Dlinter.all=false --run run_test.lean -p "$(realpath "$FILE")"
check_exit_is_success
check_out_file
