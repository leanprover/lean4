# One worker thread keeps the measurement on the code path instead of on thread wake-ups,
# which `http_server_concurrent` measures.
export LEAN_NUM_THREADS=1

TEST_ARGS=( 200 )

if [[ -n $TEST_BENCH ]]; then
  TEST_ARGS=( 100000 )
fi
