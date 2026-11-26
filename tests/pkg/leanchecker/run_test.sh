rm -rf .lake
lake build

for f in LeanCheckerTests/*.lean; do
    module="LeanCheckerTests.$(basename "$f" .lean)"
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
