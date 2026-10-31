# `-v` prints every diverging example, so the diff against `runner.lean.out.expected` includes all
# mismatched examples. The runner exits with code 0 when all examples match the spec.
capture_only "runner.lean" \
  lean -Dlinter.all=false --run runner.lean -v spec.txt
check_exit_is_success
check_out_file
