LAKE ?= ./build/bin/lake

#-------------------------------------------------------------------------------
# Suite Targets
#-------------------------------------------------------------------------------

default: build

all: build test-all

test: check-lake test-ci test-bootstrap test-bootstrapped

test-ci: test-tests test-examples

test-tests: test-49 test-50 test-62

test-examples: test-init test-hello test-io test-deps\
	test-git test-ffi test-targets test-scripts

test-bootstrapped: test-boostrapped-hello

clean: clean-build clean-tests clean-examples

clean-tests: clean-62

clean-examples: clean-init clean-hello clean-io clean-deps\
	clean-git clean-ffi clean-targets clean-bootstrap

.PHONY: all test test-all test-tests test-examples\
	clean clean-build clean-tests clean-examples build time-build check-lake\
	test-bootstrap time-bootstrap check-bootstrap test-bootstrapped

#-------------------------------------------------------------------------------
# Build Targets
#-------------------------------------------------------------------------------

build:
	./build.sh

time-build:
	./time.sh

clean-build:
	./clean.sh

check-lake:
	$(LAKE) self-check

#-------------------------------------------------------------------------------
# Example Targets
#-------------------------------------------------------------------------------

test-init:
	cd examples/init && ./test.sh

clean-init:
	cd examples/init && ./clean.sh

test-hello:
	cd examples/hello && ./test.sh

clean-hello:
	cd examples/hello && ./clean.sh

test-io:
	cd examples/io && ./test.sh

clean-io:
	cd examples/io && ./clean.sh

test-deps:
	cd examples/deps && ./test.sh

clean-deps:
	cd examples/deps && ./clean.sh

test-git:
	cd examples/git && ./test.sh

clean-git:
	cd examples/git && ./clean.sh

test-ffi:
	cd examples/ffi && ./test.sh

clean-ffi:
	cd examples/ffi && ./clean.sh

test-targets:
	cd examples/targets && ./test.sh

clean-targets:
	cd examples/targets && ./clean.sh

test-scripts:
	cd examples/scripts && ./test.sh

test-bootstrap:
	cd examples/bootstrap && ./test.sh

package-bootstrap:
	cd examples/bootstrap && ./package.sh

clean-bootstrap:
	cd examples/bootstrap && ./clean.sh

time-bootstrap:
	cd examples/bootstrap && ./time.sh

check-bootstrap:
	cd examples/bootstrap && ./check.sh

test-boostrapped-hello:
	cd examples/hello && ./bootstrapped-test.sh

#-------------------------------------------------------------------------------
# Test Targets
#-------------------------------------------------------------------------------

test-49:
	cd test/49 && ./test.sh

test-50:
	cd test/50 && ./test.sh

test-62:
	cd test/62 && ./test.sh

clean-62:
	cd test/62 && ./clean.sh
