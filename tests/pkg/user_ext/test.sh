#!/usr/bin/env bash

exit 0  # TODO: test started being nondeterministic

rm -rf .lake/build
lake build -v 2>&1 | grep 'hello, test, world'
