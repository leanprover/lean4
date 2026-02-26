TEST_ARGS=( 15 )

if [[ -n $TEST_BENCH ]]; then
  TEST_ARGS=( 23 )
fi

set_stack_size_to_maximum
