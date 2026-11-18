# `LEAN_STACK_SIZE_KB` must also apply to threads created during runtime initialization, such as
# the libuv event loop thread (#16365). With the 1 GiB default thread stack, a single such thread
# does not fit into the address-space limit below.

# `ulimit -v` is Linux-only, and sanitizers reserve far more address space than the limit.
[[ "$OSTYPE" == linux* ]] || exit 0
[[ "$(leanc --print-cflags)" != *-fsanitize* ]] || exit 0

cat > "$TMP_DIR/main.lean" <<'EOF'
def main : IO Unit := do
  IO.sleep 1
  let t ← IO.asTask (prio := .dedicated) (pure 42)
  IO.println s!"ok {t.get.toOption.get!}"
EOF

lean --root="$TMP_DIR" --c="$TMP_DIR/main.c" "$TMP_DIR/main.lean" || fail "Failed to compile main.lean"
LEANC_SHARED_ARGS=(-leanshared -lleanshared -Wl,-rpath,"$BUILD_DIR/lib/lean")
leanc ${LEANC_OPTS-} -o "$TMP_DIR/main" "$TMP_DIR/main.c" "${LEANC_SHARED_ARGS[@]}" \
  || fail "Failed to compile main.c"

LIMIT_KB=$((768 * 1024))

out="$(ulimit -v $LIMIT_KB; LEAN_STACK_SIZE_KB=8192 "$TMP_DIR/main" 2>&1)" \
  || fail "compiled program failed under the address-space limit: $out"
[[ "$out" == "ok 42" ]] || fail "unexpected output: $out"

out="$(ulimit -v $LIMIT_KB; LEAN_STACK_SIZE_KB=8192 lean --version 2>&1)" \
  || fail "lean failed under the address-space limit: $out"
