leanc ${LEANC_OPTS-} -DNDEBUG -o "$TMP_DIR/closure_arity" closure_arity.c
run "$TMP_DIR/closure_arity"
for mode in a b c z; do
    capture_exit 1 "$TMP_DIR/closure_arity" "$mode"
    check_out_contains "INTERNAL PANIC: invalid closure arity"
done
for mode in f g; do
    capture_exit 1 "$TMP_DIR/closure_arity" "$mode"
    check_out_contains "INTERNAL PANIC: invalid number of fixed closure arguments"
done
for mode in m n p q s; do
    capture_exit 1 "$TMP_DIR/closure_arity" "$mode"
    check_out_contains "INTERNAL PANIC: too many arguments in closure application"
done
