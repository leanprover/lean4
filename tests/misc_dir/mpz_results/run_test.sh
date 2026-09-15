# Match the runtime's bignum representation when compiling against its internal headers.
MPZ_TEST_FLAGS=(-std=c++20 -O2 -I"$SRC_DIR" -I"$BUILD_DIR/include")
if [[ $(sed -n 's/^USE_GMP:BOOL=//p' "$BUILD_DIR/CMakeCache.txt") == ON ]]; then
  MPZ_TEST_GMP_INCLUDE=$(sed -n 's/^GMP_INCLUDE_DIR:PATH=//p' "$BUILD_DIR/CMakeCache.txt")
  MPZ_TEST_FLAGS+=(-DLEAN_USE_GMP -I"$MPZ_TEST_GMP_INCLUDE")
fi
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  MPZ_TEST_FLAGS+=(-Wl,-rpath,"$BUILD_DIR/lib/lean")
fi
leanc "${MPZ_TEST_FLAGS[@]}" main.cpp -leanshared -lleanshared -o main.out
./main.out
