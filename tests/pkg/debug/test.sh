#!/usr/bin/env bash

rm -rf .lake/build
# should succeed
lake exe release || exit 1
# should fail
lake exe debug && exit 1
exit 0
