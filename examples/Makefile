LAKE ?= ../build/bin/lake

all: check-lake test time-bootstrap check-bootstrap test-bootstrapped

test: test-init test-hello test-io test-deps\
	test-git test-ffi test-scripts

clean: clean-init clean-hello clean-io clean-deps\
	clean-git clean-ffi clean-bootstrap

check-lake:
	$(LAKE) self-check

test-init:
	cd init && ./test.sh

clean-init:
	cd init && ./clean.sh

test-hello:
	cd hello && ./test.sh

clean-hello:
	cd hello && ./clean.sh

test-io:
	cd io && ./test.sh

clean-io:
	cd io && ./clean.sh

test-deps:
	cd deps && ./test.sh

clean-deps:
	cd deps && ./clean.sh

test-git:
	cd git && ./test.sh

clean-git:
	cd git && ./clean.sh

test-ffi:
	cd ffi && ./test.sh

clean-ffi:
	cd ffi && ./clean.sh

test-scripts:
	cd scripts && ./test.sh

test-bootstrap:
	cd bootstrap && ./test.sh

package-bootstrap:
	cd bootstrap && ./package.sh

clean-bootstrap:
	cd bootstrap && ./clean.sh

time-bootstrap:
	cd bootstrap && ./time.sh

check-bootstrap:
	cd bootstrap && ./check.sh

test-bootstrapped: test-boostrapped-hello

test-boostrapped-hello:
	cd hello && ./bootstrapped-test.sh

.PHONY: all check-lake test clean\
	test-bootstrap time-bootstrap check-bootstrap test-bootstrapped
