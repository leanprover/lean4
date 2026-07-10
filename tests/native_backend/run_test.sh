source_init "$1"

arch="$(uname -m)"
if [[ "$arch" != "arm64" && "$arch" != "aarch64" ]]; then
  echo "skipping ARM64 backend on host architecture $arch"
  exit 0
fi

base="${1%.lean}"
asm="_tmp_${base}.s"
shim="_tmp_${base}_shim.c"
exe="_tmp_${base}.out"

cleanup() {
  rm -f "$asm" "$shim" "$exe"
}
trap cleanup EXIT

lean --arm64="$asm" -Dcompiler.postponeCompile=false "$1" ||
  fail "Failed to compile $1 into ARM64 assembly"

module_init="$(awk '/[.]globl _initialize_/ { print $2; exit }' "$asm")"
if [[ -z "$module_init" ]]; then
  fail "Could not locate the module initializer in $asm"
fi

cat > "$shim" <<EOF
#include <lean/lean.h>

extern lean_object *lean_native_backend_test_main(lean_object *);
extern lean_object *${module_init#_}(uint8_t, lean_object *);
extern char **lean_setup_args(int, char **);
extern void lean_initialize(void);

int main(int argc, char **argv) {
    lean_object *result;
    argv = lean_setup_args(argc, argv);
    lean_initialize();
    lean_set_panic_messages(false);
    result = ${module_init#_}(1, lean_io_mk_world());
    lean_set_panic_messages(true);
    lean_io_mark_end_initialization();
    if (lean_io_result_is_ok(result)) {
        lean_dec_ref(result);
        lean_init_task_manager();
        result = lean_native_backend_test_main(lean_io_mk_world());
    }
    lean_finalize_task_manager();
    if (lean_io_result_is_ok(result)) {
        lean_dec_ref(result);
        return 0;
    }
    lean_io_result_show_error(result);
    lean_dec_ref(result);
    return 1;
}
EOF

leanc ${LEANC_OPTS-} -O3 -DNDEBUG -o "$exe" "$asm" "$shim" ||
  fail "Failed to link ARM64 assembly for $1"

capture_only "$1" "./$exe"
check_out_file
