capture_only "$1" \
  lean -Dlinter.all=false "$1"
check_out_file
check_exit_is_success
