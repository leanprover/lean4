if [[ "$OSTYPE" == "cygwin" || "$OSTYPE" == "msys" ]]; then
  echo "Skipped: uses POSIX threads"
  exit 0
fi
leanc ${LEANC_OPTS-} -o task_manager_cycles.produced task_manager_cycles.c
run ./task_manager_cycles.produced
capture_only "" ./task_manager_cycles.produced finalize_from_task
check_exit_is 1
check_out_contains "INTERNAL PANIC: the task manager cannot be finalized from a task"
