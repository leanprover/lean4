make -C "$BUILD_DIR" leanchecker-paranoid -j$NPROC  # as in CI
make -C "$BUILD_DIR" install DESTDIR="$(realpath install)"
python measure_sizes.py "$SRC_DIR" "$BUILD_DIR" install measurements.jsonl
rm -rf install
