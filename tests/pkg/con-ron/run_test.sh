# `con-ron` is bundled into release toolchains only, where the build injects it into `bin/` before
# installing. Skip rather than fail when absent, so an ordinary test run needs neither the binary nor
# the network to build it.
if ! command -v con-ron > /dev/null; then
    echo "con-ron not built; skipping"
    exit 0
fi

leanexport Init > "$TMP_DIR/export.ndjson"
con-ron "$TMP_DIR/export.ndjson" | tee "$TMP_DIR/out"
grep -qE '^con-ron: accepted [1-9][0-9]* declarations' "$TMP_DIR/out"
