TEST_ARGS=( 15 )

if [[ -n $TEST_BENCH ]]; then
  TEST_ARGS=( 23 )
fi

ulimit -s unlimited
