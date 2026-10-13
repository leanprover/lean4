# `lean4lean` is bundled into release toolchains only, where the build injects it into `bin/` before
# installing. Skip rather than fail when absent, so an ordinary test run needs neither the binary nor
# the network to build it.
if ! command -v lean4lean > /dev/null; then
    echo "lean4lean not built; skipping"
    exit 0
fi

# `--import` replays into an empty environment, so this re-adds every kernel-accelerated primitive
# and exercises the checker's model of them, which drifts silently as Lean's definitions change:
# `lean4lean` keeps building against its own pinned toolchain either way.
leanexport Init > "$TMP_DIR/export.txt"
lean4lean --import "$TMP_DIR/export.txt" | tee "$TMP_DIR/out"
grep -qE '^checked [1-9][0-9]* declarations$' "$TMP_DIR/out"
