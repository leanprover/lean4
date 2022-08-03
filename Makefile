LAKE ?= ./build/bin/lake

#-------------------------------------------------------------------------------
# Suite Targets
#-------------------------------------------------------------------------------

default: build

all: build test

test: check-lake test-ci test-bootstrap test-bootstrapped

test-ci: test-tests test-examples

test-tests: test-44 test-49 test-50 test-62 test-75 test-102 test-104\
	test-manifest test-meta

test-examples: test-init test-hello test-deps\
	test-git test-ffi test-targets test-precompile test-scripts

test-bootstrapped: test-boostrapped-hello

clean: clean-build clean-tests clean-examples

clean-tests: clean-44 clean-62 clean-102 clean-104 clean-manifest

clean-examples: clean-init clean-hello clean-deps\
	clean-git clean-ffi clean-targets clean-precompile clean-bootstrap

.PHONY: all test test-ci test-tests test-examples\
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

test-precompile:
	cd examples/precompile && ./test.sh

clean-precompile:
	cd examples/precompile && ./clean.sh

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

clean-44:
	cd test/44 && ./clean.sh

test-44:
	cd test/44 && ./test.sh

test-49:
	cd test/49 && ./test.sh

test-50:
	cd test/50 && ./test.sh

test-62:
	cd test/62 && ./test.sh

clean-62:
	cd test/62 && ./clean.sh

test-75:
	cd test/75 && ./test.sh

clean-102:
	cd test/102 && ./clean.sh

test-102:
	cd test/102 && ./test.sh

clean-104:
	cd test/104 && ./clean.sh

test-104:
	cd test/104 && ./test.sh

clean-manifest:
	cd test/manifest && ./clean.sh

test-manifest:
	cd test/manifest && ./test.sh

test-meta:
	cd test/meta && ./test.sh
