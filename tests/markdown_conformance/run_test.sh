# With `-v`, every diverging example is printed to stdout, so a regression
# turning a passing example into a failing one (or vice versa) shows up
# example-level in the diff against `runner.lean.out.expected`, not merely
# as a per-section tally shift. The runner exits 0 when every non-skipped
# example matches the spec.
capture_only "runner.lean" \
  lean -Dlinter.all=false --run runner.lean -v spec.txt
check_exit_is_success
check_out_file
