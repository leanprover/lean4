rm -rf .lake
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

    if [[ -f "$f.export" ]]; then
        export_file="$TMP_DIR/$module.jsonl"
        export_err="$TMP_DIR/$module.err"
        lake env leanexport "$module" -- $(cat "$f.export") > "$export_file" 2> "$export_err"
        if [[ -s "$export_err" ]]; then
            cat "$export_err"
            fail "leanexport failed for $module"
        fi

        capture_only "$f.export" \
          lake env leanchecker --from-export "$export_file"
        check_out_file
        if grep -q "accepts the solution" "$f.export.out.produced"; then
            check_exit_is_success
        else
            check_exit_is_fail
        fi
    fi
done
