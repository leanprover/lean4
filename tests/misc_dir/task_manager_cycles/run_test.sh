if [[ "$OSTYPE" == "cygwin" || "$OSTYPE" == "msys" ]]; then
  echo "Skipped: uses POSIX threads"
  exit 0
fi
leanc ${LEANC_OPTS-} -o task_manager_cycles.produced task_manager_cycles.c
run ./task_manager_cycles.produced
capture_only "" ./task_manager_cycles.produced finalize_from_task
check_exit_is 1
check_out_contains "INTERNAL PANIC: the task manager cannot be finalized from a task"
capture_only "" ./task_manager_cycles.produced result_dropped_on_loop
check_exit_is 1
check_out_contains "would block the event loop thread"
capture_only "" lean --run throw_in_sync_task.lean
check_exit_is 1
check_out_contains "Could not find native implementation"
