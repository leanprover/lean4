# `nanoda_bin` is bundled into release toolchains only, where the build injects it into `bin/` before
# installing. Skip rather than fail when absent, so an ordinary test run needs neither the binary nor
# the network to build it.
if ! command -v nanoda_bin > /dev/null; then
    echo "nanoda not built; skipping"
    exit 0
fi

# `nanoda_bin` is configured by a JSON file rather than by flags. Its kernel extensions are off by
# default; turning them on is what exercises its model of Lean's `Nat` and `String` primitives, which
# drifts silently as Lean's definitions change: `nanoda` keeps building either way. `sorryAx` is
# exported but never used, so an axiom outside the permitted list must not be fatal, and the
# default-on axiom listing needs a destination or it is reported as a pretty printer error.
cat > "$TMP_DIR/config.json" <<'EOF'
{
  "use_stdin": true,
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "unpermitted_axiom_hard_error": false,
  "nat_extension": true,
  "string_extension": true,
  "pp_to_stdout": true,
  "print_success_message": true
}
EOF

leanexport Init | nanoda_bin "$TMP_DIR/config.json" | tee "$TMP_DIR/out"
grep -qE '^Checked [1-9][0-9]* declarations with no errors' "$TMP_DIR/out"
