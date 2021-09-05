LAKE := ../build/bin/lake

test: verify-lake test-init test-hello test-io test-deps test-git test-ffi test-bootstrap test-boostrap-hello

.PHONY: test

verify-lake:
	$(LAKE) self-check

test-init:
	cd init && ./test.sh

test-hello:
	cd hello && ./test.sh

test-io:
	cd io && ./test.sh

test-deps:
	cd deps && ./test.sh

test-git:
	cd git && ./test.sh

test-ffi:
	cd ffi && ./test.sh

time-bootstrap:
	cd bootstrap && ./time.sh

test-bootstrap:
	cd bootstrap && ./test.sh

test-boostrap-hello:
	cd hello && ./bootstrap-test.sh
