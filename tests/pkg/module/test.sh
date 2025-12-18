#!/usr/bin/env bash
set -e

rm -rf .lake/build
LEAN_ABORT_ON_PANIC=1 lake build
lake lean Module/ConflictingImported.lean | grep "already contains 'f'"
