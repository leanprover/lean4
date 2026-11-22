if [[ "$OSTYPE" == "cygwin" || "$OSTYPE" == "msys" ]]; then
  echo "Skipped: uses SIGWINCH and usleep"
  exit 0
fi
leanc ${LEANC_OPTS-} -o uv_restart.produced uv_restart.c
run ./uv_restart.produced
run ./uv_restart.produced exit_during_teardown
for mode in wait_exited_child_from_loop wait_across_teardown zombies failed_restart signal_during_teardown; do
  run ./uv_restart.produced "$mode"
done
capture_only "" ./uv_restart.produced finalize_on_loop_thread
check_exit_is 1
check_out_contains "INTERNAL PANIC: the task manager cannot be finalized"
