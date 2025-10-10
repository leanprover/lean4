#!/usr/bin/env bash
source ../common.sh

./clean.sh

# Test failure log level

echo "# TEST: Failure log level"

log_fail_target() {
  test_err "foo" build "$@"
  test_err "foo" build "$@" # test replay
}

log_fail_target topTrace --fail-level=trace
log_fail_target artTrace --fail-level=trace

log_fail() {
  lv=$1; shift
  log_fail_target top$lv "$@"
  log_fail_target art$lv "$@"
  log_fail_target Log.$lv "$@"
}

log_fail Info --iofail
log_fail Warning --wfail
log_fail Error

# Test output log level

echo "# TEST: Output log level"

log_empty() {
  lv=$1; shift
  rm -f .lake/build/art$lv
  test_not_out "foo" build art$lv "$@"
  test_run build art$lv -v # test whole log was saved
  test_not_out "foo" build art$lv "$@" # test replay
}

log_empty Info -q
log_empty Info --log-level=warning
log_empty Warning --log-level=error

log_empty Trace -q
log_empty Trace --log-level=info
log_empty Trace

# Test configuration-time output log level

echo "# TEST: Configuration log level"
test_out "info:" resolve-deps -R -Klog=info
test_not_out "info:" resolve-deps -R -Klog=info -q
test_out "warning:" resolve-deps -R -Klog=warning
test_not_out "warning:" resolve-deps -R -Klog=warning --log-level=error
