source_init "$1"

if [[ -f "$1.do_compile_test" ]]; then DO_COMPILE=1
elif [[ -f "$1.no_compile_test" ]]; then DO_COMPILE=
elif [[ -f "$1.do_compile" ]]; then DO_COMPILE=1
elif [[ -f "$1.no_compile" ]]; then DO_COMPILE=
else DO_COMPILE=1
fi

if [[ -f "$1.do_interpret_test" ]]; then DO_INTERPRET=1
elif [[ -f "$1.no_interpret_test" ]]; then DO_INTERPRET=
elif [[ -f "$1.do_interpret" ]]; then DO_INTERPRET=1
elif [[ -f "$1.no_interpret" ]]; then DO_INTERPRET=
else DO_INTERPRET=1
fi

if [[ -n $DO_COMPILE ]]; then
  echo "Compiling and executing lean file"
  run_before "$1"

  lean --c="$1.c" -Dcompiler.postponeCompile=false "${TEST_LEAN_ARGS[@]}" "$1" || fail "Failed to compile $1 into $1.c"
  leanc ${LEANC_OPTS-} -O3 -DNDEBUG -o "$1.out" "${TEST_LEANC_ARGS[@]}" "$1.c" || fail "Failed to compile $1.c"

  capture_only "$1" \
    "./$1.out" "${TEST_ARGS[@]}"
  normalize_measurements
  check_out_file
  check_exit_is "${TEST_EXIT:-0}"

  run_after "$1"
fi

if [[ -n $DO_INTERPRET ]]; then
  echo "Interpreting lean file"
  run_before "$1"

  capture_only "$1" \
    lean -Dlinter.all=false "${TEST_LEANI_ARGS[@]}" --run "$1" "${TEST_ARGS[@]}"
  normalize_measurements
  check_out_file
  check_exit_is "${TEST_EXIT:-0}"

  run_after "$1"
fi
