# Deterministically fail the compactor's initial and growth allocations. The
# linker's --wrap option makes this a Linux-only native regression test.
case "$($CXX -dumpmachine)" in
    *linux*) ;;
    *) return ;;
esac

compactor_test_dir="$TMP_DIR/compactor_oom"
mkdir -p "$compactor_test_dir"
# The compactor always uses libc malloc. Build its allocation path directly,
# independent of the configured allocator for small Lean objects.
# Preinclude the build's config so CXX's existing include flags cannot
# re-enable mimalloc after the override.
printf '#include <lean/config.h>\n#undef LEAN_MIMALLOC\n' \
    > "$compactor_test_dir/config.h"
# Release builds bundle the C++ runtime in the stage's lib directory.
$CXX -std=c++20 -O2 -DNDEBUG -DLEAN_MULTI_THREAD \
    -ffunction-sections -fdata-sections \
    -include "$compactor_test_dir/config.h" \
    -I "$SRC_DIR" -I "$SRC_DIR/include" -I "$BUILD_DIR/include" \
    "$TEST_DIR/misc/compactor_oom.cpp" "$SRC_DIR/runtime/compact.cpp" \
    "$SRC_DIR/runtime/hash.cpp" "$SRC_DIR/runtime/object.cpp" \
    -Wl,--gc-sections -Wl,--wrap=malloc -Wl,-rpath,"$BUILD_DIR/lib" \
    -o "$compactor_test_dir/test"

"$compactor_test_dir/test" control
printf 'INTERNAL PANIC: out of memory\n' > "$compactor_test_dir/expected"
for allocation in initial growth; do
    status=0
    env -u LEAN_ABORT_ON_PANIC "$compactor_test_dir/test" "$allocation" \
        > "$compactor_test_dir/output" 2>&1 || status=$?
    test "$status" -eq 1
    diff -u "$compactor_test_dir/expected" "$compactor_test_dir/output"
done
