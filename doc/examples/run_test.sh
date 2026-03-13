capture_only "$1" \
  lean -Dlinter.all=false "$1"
check_exit_is_success
check_out_file
