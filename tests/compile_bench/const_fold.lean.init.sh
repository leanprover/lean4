TEST_ARGS=( 15 )

if [[ -n $TEST_BENCH ]]; then
  TEST_ARGS=( 23 )
fi

# When interpreted
set_stack_size_to_maximum

# When compiled
export LEAN_STACK_SIZE_KB=4194304
