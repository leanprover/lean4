source_init "$1"

if [[ "$1" == "ui_abi.lean" ]]; then
  mkdir -p _tmp_ui_abi
  trap 'rm -f _tmp_ui_abi/UiAbi.ir _tmp_ui_abi/UiAbi.ir.sig _tmp_ui_abi/UiAbi.olean _tmp_ui_abi/UiAbi.ilean _tmp_ui_abi/UiAbi.olean.private _tmp_ui_abi/UiAbi.olean.server; rmdir _tmp_ui_abi 2>/dev/null || true' EXIT
  lean -o _tmp_ui_abi/UiAbi.olean UiAbi.lean || fail "Failed to compile UI ABI module"
  capture_only "$1" env LEAN_PATH="_tmp_ui_abi:${LEAN_PATH-}" lean "$1"
  check_out_file
  exit 0
fi

# Reactor modules have no `_start`; wasm-interp still prints a harmless WASI notice.
filter_wasi_noise() {
  local f="$1.out.produced"
  if [[ -f "$f" ]]; then
    grep -v '^wasi error: _start export not found$' "$f" > "${f}.tmp" || true
    mv "${f}.tmp" "$f"
  fi
}

if [[ "$1" == "encoding.lean" ]]; then
  capture_only "$1" lean "$1"
  check_out_file
  exit 0
fi

RUNTIME_TESTS="object.lean|boxing.lean|closure.lean|reuse.lean|string.lean|big_nat.lean|array.lean|high_arity.lean|core_rt.lean|closed_const.lean"
if [[ "$1" =~ ^($RUNTIME_TESTS)$ && -z "${WASI_SDK_PATH-}" ]]; then
  echo "skipping runtime-backed WebAssembly test without WASI_SDK_PATH"
  exit 0
fi

wasm="_tmp_${1%.lean}.wasm"
linked="_tmp_${1%.lean}.linked.wasm"
external_obj="_tmp_${1%.lean}_WasmExternal.wasm"
init_linked="_tmp_${1%.lean}.init.linked.wasm"
external_dir="_tmp_${1%.lean}_deps"
external_olean="$external_dir/WasmExternal.olean"
trap 'rm -f "$wasm" "$linked" "$init_linked" "$external_obj" "$external_olean" "$external_dir/WasmExternal.ir" "$external_dir/WasmExternal.ir.sig" "$external_dir/WasmExternal.olean.private" "$external_dir/WasmExternal.olean.server"; rmdir "$external_dir" 2>/dev/null || true' EXIT

if [[ "$1" == "cross_module.lean" ]]; then
  mkdir -p "$external_dir"
  lean -o "$external_olean" --wasm="$external_obj" WasmExternal.lean ||
    fail "Failed to compile external WebAssembly test module"
  LEAN_PATH="$external_dir:${LEAN_PATH-}" lean --wasm="$wasm" "$1" ||
    fail "Failed to compile $1 to WebAssembly"
elif [[ "$1" == "core_rt.lean" ]]; then
  mkdir -p "$external_dir"
  lean -o "$external_dir/core_rt_lib.olean" --wasm="$external_dir/core_rt_lib.wasm" core_rt_lib.lean ||
    fail "Failed to compile core_rt_lib WebAssembly module"
  LEAN_PATH="$external_dir:${LEAN_PATH-}" lean --wasm="$wasm" "$1" ||
    fail "Failed to compile $1 to WebAssembly"
else
  lean --wasm="$wasm" "$1" || fail "Failed to compile $1 to WebAssembly"
fi

wasm-validate "$wasm" || fail "Generated module failed WebAssembly validation"
wasm-objdump -x "$wasm" | grep -q 'name: "linking"' ||
  fail "Generated module is missing WebAssembly object linking metadata"
if [[ "$1" == "basic.lean" ]]; then
  wasm_ld="${WASM_LD:-/opt/homebrew/opt/lld/bin/wasm-ld}"
  "$wasm_ld" --no-entry --export=lean_wasm_add -o "$linked" "$wasm" ||
    fail "Failed to link generated WebAssembly object"
  wasm-validate "$linked" || fail "Linked module failed WebAssembly validation"
  capture_only "$1" wasm-interp "$linked" -r lean_wasm_add -a i32:20 -a i32:22
elif [[ "$1" == "primitives.lean" ]]; then
  wasm_ld="${WASM_LD:-/opt/homebrew/opt/lld/bin/wasm-ld}"
  "$wasm_ld" --no-entry \
    --export=lean_wasm_prim_div --export=lean_wasm_prim_mod \
    --export=lean_wasm_prim_and --export=lean_wasm_prim_or --export=lean_wasm_prim_xor \
    --export=lean_wasm_prim_shl --export=lean_wasm_prim_shr \
    -o "$linked" "$wasm" || fail "Failed to link primitive WebAssembly object"
  wasm-validate "$linked" || fail "Linked module failed WebAssembly validation"
  capture_only "$1" bash -c '
    wasm-interp "$0" -r lean_wasm_prim_div -a i32:42 -a i32:5
    wasm-interp "$0" -r lean_wasm_prim_mod -a i32:42 -a i32:5
    wasm-interp "$0" -r lean_wasm_prim_and -a i32:240 -a i32:15
    wasm-interp "$0" -r lean_wasm_prim_or -a i32:240 -a i32:15
    wasm-interp "$0" -r lean_wasm_prim_xor -a i32:255 -a i32:15
    wasm-interp "$0" -r lean_wasm_prim_shl -a i32:3 -a i32:2
    wasm-interp "$0" -r lean_wasm_prim_shr -a i32:40 -a i32:2
  ' "$linked"
elif [[ "$1" == "control.lean" ]]; then
  wasm_ld="${WASM_LD:-/opt/homebrew/opt/lld/bin/wasm-ld}"
  "$wasm_ld" --no-entry --export=lean_wasm_choose_zero --export=lean_wasm_choose_one \
    -o "$linked" "$wasm" || fail "Failed to link generated WebAssembly object"
  wasm-validate "$linked" || fail "Linked module failed WebAssembly validation"
  capture_only "$1" wasm-interp "$linked" --run-all-exports
elif [[ "$1" == "multicase.lean" ]]; then
  wasm_ld="${WASM_LD:-/opt/homebrew/opt/lld/bin/wasm-ld}"
  "$wasm_ld" --no-entry --export=lean_wasm_multicase_0 --export=lean_wasm_multicase_1 \
    --export=lean_wasm_multicase_2 -o "$linked" "$wasm" ||
    fail "Failed to link multi-constructor WebAssembly object"
  wasm-validate "$linked" || fail "Linked module failed WebAssembly validation"
  capture_only "$1" wasm-interp "$linked" --run-all-exports
elif [[ "$1" == "cross_module.lean" ]]; then
  wasm_ld="${WASM_LD:-/opt/homebrew/opt/lld/bin/wasm-ld}"
  "$wasm_ld" --no-entry --export=lean_wasm_cross_module -o "$linked" "$external_obj" "$wasm" ||
    fail "Failed to link cross-module WebAssembly objects"
  wasm-validate "$linked" || fail "Linked module failed WebAssembly validation"
  if [[ -n "${WASI_SDK_PATH-}" ]]; then
    leanc --target=wasm32-wasip1 -Wl,--export=initialize_cross__module -o "$init_linked" \
      "$external_obj" "$wasm" || fail "Failed to link cross-module initializer chain"
    wasm-validate --enable-exceptions "$init_linked" ||
      fail "Linked cross-module initializer chain failed WebAssembly validation"
  fi
  capture_only "$1" wasm-interp "$linked" -r lean_wasm_cross_module -a i32:41
else
  if [[ ! -f "$BUILD_DIR/wasm32-wasip1/libleanrt.a" ]]; then
    "$SCRIPT_DIR/build_wasm_runtime.sh" "$BUILD_DIR/wasm32-wasip1" ||
      fail "Failed to build wasm32-wasip1 Lean runtime"
  fi
  if [[ "$1" == "core_rt.lean" ]]; then
    leanc --target=wasm32-wasip1 -o "$linked" \
      "$external_dir/core_rt_lib.wasm" "$wasm" ||
      fail "Failed to link multi-module core-runtime WebAssembly program"
  else
    leanc --target=wasm32-wasip1 -o "$linked" "$wasm" ||
      fail "Failed to link runtime-backed WebAssembly object"
  fi
  wasm-validate --enable-exceptions "$linked" || fail "Linked module failed WebAssembly validation"
  if [[ "$1" == "object.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_object_sum -a i32:20 -a i32:22
  elif [[ "$1" == "boxing.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_box_roundtrip -a i32:42
  elif [[ "$1" == "closure.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_closure -a i32:20 -a i32:22
  elif [[ "$1" == "reuse.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_reuse -a i32:10 -a i32:20 -a i32:7
  elif [[ "$1" == "string.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_string_size -a i32:0
  elif [[ "$1" == "big_nat.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_big_nat -a i32:5
  elif [[ "$1" == "high_arity.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_high_arity
  elif [[ "$1" == "closed_const.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_closed_lit
  elif [[ "$1" == "core_rt.lean" ]]; then
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_core_rt -a i32:20 -a i32:22
  else
    capture_only "$1" wasm-interp "$linked" --enable-exceptions --wasi \
      -r lean_wasm_array_sum -a i32:20 -a i32:22
  fi
fi
filter_wasi_noise "$1"
check_out_file
