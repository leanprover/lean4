LAKE ?= ./build/bin/lake

#-------------------------------------------------------------------------------
# Suite Targets
#-------------------------------------------------------------------------------

TESTS := $(addprefix test/, $(shell ls test))
EXAMPLES := $(addprefix examples/, $(filter-out bootstrap, $(shell ls examples)))

default: build

all: build test

test: check-lake test-ci test-bootstrap test-bootstrapped

test-ci: test-tests test-examples

test-tests: $(addsuffix .test, $(TESTS))

test-examples: $(addsuffix .test, $(EXAMPLES))

test-bootstrapped: test-boostrapped-hello

clean: clean-tests clean-examples clean-build

clean-tests: $(addsuffix .clean, $(TESTS))

clean-examples:  $(addsuffix .clean, $(EXAMPLES))

.PHONY:
	all test test-ci test-tests test-examples\
	test-bootstrap time-bootstrap check-bootstrap test-bootstrapped test-boostrapped-hello\
	$(addsuffix .clean, $(TESTS) $(EXAMPLES)) $(addsuffix .test, $(TESTS))

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
# Test / Example Targets
#-------------------------------------------------------------------------------

test/%.test:
	cd test/$* && ./test.sh

test/%.clean:
	cd test/$* && ./clean.sh

examples/%.test:
	cd examples/$* && ./test.sh

examples/%.clean:
	cd examples/$* && ./clean.sh

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
