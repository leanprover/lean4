#!/usr/bin/env bash
source ../common.sh

export LEAN_ABORT_ON_PANIC=1
ulimit -c 0

# Both export computations must wait for pending metadata without blocking a
# synchronous task and retain the jobs captured before artifact completion.
for facet in export meta; do
  for mode in pending replace; do
    test_out "export metadata checked" run probe "$facet" imports "$mode"
  done
  test_status_out 1 "metadata failed" run probe "$facet" imports fail
  test_out "export metadata checked" run probe "$facet" imports cancel
done

for mode in pending replace; do
  test_out "export metadata checked" run probe export input "$mode"
done
test_status_out 1 "metadata failed" run probe export input fail
test_out "export metadata checked" run probe export input cancel
