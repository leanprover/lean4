LAKE := ../build/bin/lake

all: check-lake test time-bootstrap check-bootstrap test-bootstrapped

test: test-init test-hello test-io test-deps test-git test-ffi

check-lake:
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

test-bootstrap:
	cd bootstrap && ./test.sh

time-bootstrap:
	cd bootstrap && ./time.sh

check-bootstrap:
	cd bootstrap && ./check.sh

test-bootstrapped: test-boostrapped-hello

test-boostrapped-hello:
	cd hello && ./bootstrapped-test.sh

.PHONY: all check-lake test time-bootstrap check-bootstrap test-bootstrapped
