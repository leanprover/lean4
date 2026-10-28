# Compile the fallback directly so these checks also run in GMP-backed builds.
# Use the standard allocator and disable debug assertions to exercise the runtime guards.
cat > "$TMP_DIR/non_gmp_config.h" <<'EOF'
#include <lean/config.h>
#undef LEAN_USE_GMP
#undef LEAN_MIMALLOC
#undef LEAN_DEBUG
EOF

read -r -a mpz_test_compiler <<< "$CXX"
mpz_test_linker_flags=()
if [[ $(uname -s) == Linux ]]; then
    # Standalone Linux builds bundle libc++ in the build's library directory.
    mpz_test_linker_flags+=("-Wl,-rpath,$BUILD_DIR/lib")
fi
"${mpz_test_compiler[@]}" -std=c++20 -DNDEBUG -DLEAN_MULTI_THREAD -I"$SRC_DIR" -I"$BUILD_DIR/include" \
    -include "$TMP_DIR/non_gmp_config.h" \
    main.cpp "$SRC_DIR/runtime/mpz.cpp" "$SRC_DIR/runtime/mpn.cpp" \
    "$SRC_DIR/runtime/exception.cpp" "${mpz_test_linker_flags[@]}" -o "$TMP_DIR/mpz_signs"
"$TMP_DIR/mpz_signs"
