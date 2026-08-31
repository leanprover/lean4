TEST_ARGS=( ../../src/Init/Prelude.lean 2 )

if [[ -n $TEST_BENCH ]]; then
  TEST_ARGS=( ../../src/Init/Prelude.lean 50 )
fi
