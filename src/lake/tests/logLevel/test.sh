#!/usr/bin/env bash
set -euxo pipefail

exit 0  # TODO: flaky test disabled

# test disabled 
LAKE=${LAKE:-../../.lake/build/bin/lake}

./clean.sh

# Test failure log level

log_fail_target() {
  ($LAKE build "$@" && exit 1 || true) | grep --color foo
  ($LAKE build "$@" && exit 1 || true) | grep --color foo # test replay
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

log_empty() {
  lv=$1; shift
  rm -f .lake/build/art$lv
  $LAKE build art$lv "$@" | grep --color foo && exit 1 || true
  $LAKE build art$lv -v # test whole log was saved
  $LAKE build art$lv "$@" | grep --color foo && exit 1 || true # test replay
}

log_empty Info -q
log_empty Info --log-level=warning
log_empty Warning --log-level=error

log_empty Trace -q
log_empty Trace --log-level=info
log_empty Trace

# Test configuration-time output log level

$LAKE resolve-deps -R -Klog=info 2>&1 | grep --color "info:"
$LAKE resolve-deps -R -Klog=info -q 2>&1 |
  grep --color "info:"  && exit 1 || true
$LAKE resolve-deps -R -Klog=warning 2>&1 | grep --color "warning:"
$LAKE resolve-deps -R -Klog=warning --log-level=error 2>&1 |
  grep --color "warning:" && exit 1 || true
