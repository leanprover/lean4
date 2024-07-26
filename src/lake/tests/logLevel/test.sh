#!/usr/bin/env bash
set -euxo pipefail

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
  log_fail_target top${lv^} "$@"
  log_fail_target art${lv^} "$@"
  log_fail_target Log.${lv^} "$@"
}

log_fail info --iofail
log_fail warning --wfail
log_fail error

# Test output log level

log_empty() {
  lv=$1; shift
  rm -f .lake/build/art_$lv
  $LAKE build art${lv^} "$@" | grep --color foo && exit 1 || true
  $LAKE build art${lv^} -v # test whole log was saved
  $LAKE build art${lv^} "$@" | grep --color foo && exit 1 || true # test replay
}

log_empty info -q
log_empty info --log-level=warning
log_empty warning --log-level=error

log_empty trace -q
log_empty trace --log-level=info
log_empty trace

# Test configuration-time output log level

$LAKE resolve-deps -R -Klog=info 2>&1 | grep --color "info: bar"
$LAKE resolve-deps -R -Klog=info -q 2>&1 |
  grep --color "info: bar"  && exit 1 || true
$LAKE resolve-deps -R -Klog=warning 2>&1 | grep --color "warning: bar"
$LAKE resolve-deps -R -Klog=warning --log-level=error 2>&1 |
  grep --color "warning: bar" && exit 1 || true
