# Deterministically fail the compactor's initial and growth allocations. The
# linker's --wrap option makes this a Linux-only native regression test.
case "$($CXX -dumpmachine)" in
    *linux*) ;;
    *) return ;;
esac

compactor_test_dir=$(mktemp -d)
trap 'rm -rf "$compactor_test_dir"' EXIT
mkdir -p "$compactor_test_dir/lean"
# The compactor always uses libc malloc. Build its allocation path directly,
# independent of the configured allocator for small Lean objects.
sed '/^#define LEAN_MIMALLOC/d' "$BUILD_DIR/include/lean/config.h" \
    > "$compactor_test_dir/lean/config.h"
$CXX -std=c++20 -O2 -DNDEBUG -DLEAN_MULTI_THREAD \
    -ffunction-sections -fdata-sections \
    -I "$compactor_test_dir" -I "$SRC_DIR" -I "$SRC_DIR/include" -I "$BUILD_DIR/include" \
    "$TEST_DIR/misc/compactor_oom.cpp" "$SRC_DIR/runtime/compact.cpp" \
    "$SRC_DIR/runtime/hash.cpp" "$SRC_DIR/runtime/object.cpp" \
    -Wl,--gc-sections -Wl,--wrap=malloc -o "$compactor_test_dir/test"

"$compactor_test_dir/test" control
printf 'INTERNAL PANIC: out of memory\n' > "$compactor_test_dir/expected"
for allocation in initial growth; do
    status=0
    env -u LEAN_ABORT_ON_PANIC "$compactor_test_dir/test" "$allocation" \
        > "$compactor_test_dir/output" 2>&1 || status=$?
    test "$status" -eq 1
    diff -u "$compactor_test_dir/expected" "$compactor_test_dir/output"
done
