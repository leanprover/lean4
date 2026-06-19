# IO.Process.exit (used by the file worker) seems to be incompatible with LSAN
# TODO: investigate or work around
export ASAN_OPTIONS=detect_leaks=0

source_init "$1"

# these tests don't have to succeed
capture_only "$1" \
  lean -Dlinter.all=false --run run_test.lean "$1"
normalize_mvar_suffixes
normalize_reference_urls
check_out_file
check_exit_is "${TEST_EXIT:-0}"
