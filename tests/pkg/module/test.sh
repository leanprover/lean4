#!/usr/bin/env bash

rm -rf .lake/build
LEAN_ABORT_ON_PANIC=1 lake build
