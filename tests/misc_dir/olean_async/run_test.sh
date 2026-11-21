# The `.olean` output of a module must not depend on `Elab.async`.
# Linters stay enabled as their results are part of the output.
capture lean -o "$TMP_DIR/async.olean" OleanAsync.lean
check_out_file
capture lean -DElab.async=false -o "$TMP_DIR/sync.olean" OleanAsync.lean
check_out_file

for part in "" .server .private; do
  cmp "$TMP_DIR/async.olean$part" "$TMP_DIR/sync.olean$part" ||
    fail "OleanAsync.olean$part depends on Elab.async"
done
