# `IO.getProgramName` returns `argv[0]`, which the caller chooses (issue #5819).

function check_out_is {
  printf '%s\n' "$@" | $DIFF -- - "$CAPTURED.out.produced" || fail "Unexpected output"
}

LEANC_SHARED_ARGS=(-leanshared -lleanshared)
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  LEANC_SHARED_ARGS+=(-Wl,-rpath,"$BUILD_DIR/lib/lean")
fi
lean --c=ProgramName.c -Dcompiler.postponeCompile=false ProgramName.lean
leanc ${LEANC_OPTS-} -o ProgramName.produced ProgramName.c "${LEANC_SHARED_ARGS[@]}"
leanc ${LEANC_OPTS-} -o Embedded.produced Embedded.c "${LEANC_SHARED_ARGS[@]}"

# MSYS passes a native Windows program the Windows path of its executable as `argv[0]`, and Windows
# has no process title in the memory of `argv`.
if [[ "$OSTYPE" != "cygwin" && "$OSTYPE" != "msys" ]]; then
  capture ./ProgramName.produced
  check_out_is ./ProgramName.produced

  capture bash -c 'exec -a secret_name ./ProgramName.produced --set-title'
  check_out_is secret_name changed secret_name

  # Outside `--run`, `lean` reports its own name.
  capture lean --stdin <<< '#eval IO.getProgramName'
  check_out_is '"lean"'
fi

# The interpreter reports the file it runs.
capture lean --run ProgramName.lean
check_out_is ProgramName.lean

# A C `main` that does not call `lean_setup_args` has no program name.
capture ./Embedded.produced
check_out_is unknown
