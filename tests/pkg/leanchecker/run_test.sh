rm -rf .lake/build
lake build

for f in LeanCheckerTests/*.lean; do
    module="LeanCheckerTests.$(basename "$f" .lean)"
    # Check for --fresh mode test
    if [[ -f "$f.fresh" ]]; then
        capture_only "$f" \
          lake env leanchecker --fresh "$module"
        check_out_file
        check_exit_is_fail
    # Check for normal mode test
    elif [[ -f "$f.out.expected" ]]; then
        # Expect failure with specific output
        capture_only "$f" \
          lake env leanchecker "$module"
        check_out_file
        check_exit_is_fail
    else
        # No expected output files - expect success (exit 0)
        run lake env leanchecker "$module"
    fi
done
