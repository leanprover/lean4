mkdir -p _tmp

run leanc ${LEANC_OPTS-} -o _tmp/native native.c
run ./_tmp/native
run leanc ${LEANC_OPTS-} -o _tmp/concurrent concurrent.c
run ./_tmp/concurrent
